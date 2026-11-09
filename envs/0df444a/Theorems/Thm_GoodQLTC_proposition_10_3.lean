-- Prove2me | Theorems.Thm_GoodQLTC_proposition_10_3
-- name    : GoodQLTC.proposition_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:56:18.255997+00:00
-- url     : https://prove2.me/theorems/ba1fb1c0-dd81-4a3b-af82-cbecdde922be
-- title:
--   Proposition 10.3: soundness on syndrome spaces
-- statement:
--   Let $X$ and $\mathcal F$ satisfy the hypotheses of Theorems 8.2 and 9.1 (a regular, $\lambda$-expanding $t$-dimensional cubical complex with degrees $2\le n_1\le\dots\le n_t$, $n_t/n_1\le\tau$, an $\mathbb F_{2^s}$-cosheaf with compatible base codes whose local families and dual local families are universally $\rho$-product-expanding, $0<\rho\le1$, $\tau\ge1$), with $t\ge4$, $2\le k\le t-2$ and $\lambda L\le 1/2$, and let $Q$ be the CSS code of Equation (4.5) with its full check list. Put $q_k:=s\,n_t^{t-k}$ and $\alpha_b:=\min\{\alpha_k,\alpha'_k\}/q_k$ with $\alpha'_k=(M_h^2/\alpha_{t-k}+M_h)^{-1}$. Then
--   $$
--   H\succeq\frac{\sigma}{N}D_Q\qquad\text{where}\qquad \sigma:=\alpha_b\frac{M_k}{M_{k-1}+M_{k+1}}>0 .
--   $$
--
--   Differences from the source:
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
--   - generalization: M_h the constant of Theorem 9.1 → any M_h ≥ 1 for which the conclusions of Theorem 9.1 hold for this X and F; reason: the constant M_h(t, n_t) of Theorem 9.1 is such an M_h; the proof uses only those conclusions
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
--   - encoding: an ordered F_2-basis β of F → an additive isomorphism F ≃ F_2^s; reason: the coordinate map of an ordered basis; every additive isomorphism of F_2-spaces is F_2-linear
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Proposition 10.3, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_GoodQLTC_IsLocallyTestable
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_IsExpanding
import Definitions.Def_GoodQLTC_BaseCodeData
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_GoodQLTC_cobdMat
import Definitions.Def_GoodQLTC_cssHX
import Definitions.Def_GoodQLTC_etaConst
open Matrix

namespace GoodQLTC

universe u

/-- **Proposition 10.3** (soundness on syndrome spaces), Gay–Jeronimo, arXiv:2609.20780 (held
version), p.32: let `X` and `F` satisfy the hypotheses of Theorems 8.2 and 9.1, with `t ≥ 4`,
`2 ≤ k ≤ t − 2` and `λL ≤ 1/2`, and let `Q` be the CSS code of Equation (4.5) with its full check
list. With `q_k := s n_t^{t−k}` and `α_b := min{α_k, α'_k}/q_k` (p.31), the testing Hamiltonian
satisfies `H ⪰ (σ/N) D_Q` where `σ := α_b M_k/(M_{k−1} + M_{k+1}) > 0`.

**Formalization Note.** The setting is that of Proposition 10.2 (§10 preamble, p.31): both
product-expansion hypotheses (primal for Theorem 8.2, dual for Theorem 9.1), the standing
assumptions of §§8–9, and `M_h ≥ 1` any constant for which the two conclusions of Theorem 9.1 hold
for this `X` and `F` (hypotheses `hsys`, `hcyc`), in particular `M_h(t, n_t)`;
`α'_k := (M_h²/α_{t−k} + M_h)^{−1}`. `M_j` is `cochainDim φ Fs j`; `N = s M_k` is the number of
columns of `H_X`. `β` is any ordered `F_2`-basis of `F` (stalk bases are the coordinates).
Soundness is `IsSound`: `H − (σ/N) D_Q` positive semidefinite on the whole Hilbert space. -/
theorem proposition_10_3 {t : ℕ} (ht : 4 ≤ t) {X : Type} [PartialOrder X] [Fintype X]
    {φ : X → Fin t → Option Bool} {n : Fin t → ℕ} (hn : ∀ i, 2 ≤ n i) (hmono : Monotone n)
    (hX : IsCubicalComplex t φ) (hreg : IsRegular φ n) (lam : ℝ) (hexp : IsExpanding φ n lam)
    {F : Type} [Field F] [Fintype F] {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ s)
    (Fs : Cosheaf X F) {m : Fin t → Bool → ℕ} (hm : ∀ i b, 0 < m i b ∧ m i b < n i)
    (D : BaseCodeData φ Fs m) (hD : IsCompatible D)
    (ρ τ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 1 ≤ τ)
    (hratio : (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ)
    (hPE : ∀ (f : X) (I : Finset (Fin t)), I.Nonempty → I ⊆ codir φ f →
      IsUnivProductExpanding.{u} ρ (fun i : I => localCode D f i.1) ∧
      IsUnivProductExpanding.{u} ρ (fun i : I => dualCode (localCode D f i.1)))
    (hlamL : lam * LConst t ρ τ ≤ 1 / 2)
    (Mh : ℝ) (hMh : 1 ≤ Mh)
    (hsys : ∀ p : ℕ, 1 ≤ p → p < t → ∀ x : Cochain φ Fs p F,
      (cobdMat φ Fs (p - 1) p)ᵀ.mulVec x = 0 →
      x ∉ LinearMap.range (cobdMat φ Fs p (p + 1))ᵀ.mulVecLin →
      etaConst t ρ τ * (numFaces φ (t - p) : ℝ) / Mh ≤ (blockWeight x : ℝ))
    (hcyc : ∀ p : ℕ, 2 ≤ p → p < t → ∀ x : Cochain φ Fs p F,
      ∃ y : Cochain φ Fs p F, (cobdMat φ Fs (p - 1) p)ᵀ.mulVec y = 0 ∧
        (Mh ^ 2 / alphaConst n ρ τ (t - p) + Mh)⁻¹ * (blockWeight (x - y) : ℝ) ≤
          (blockWeight ((cobdMat φ Fs (p - 1) p)ᵀ.mulVec x) : ℝ))
    (k : ℕ) (hk : 2 ≤ k) (hkt : k + 2 ≤ t) (β : F ≃+ (Fin s → ZMod 2)) :
    let αb : ℝ := min (alphaConst n ρ τ k) ((Mh ^ 2 / alphaConst n ρ τ (t - k) + Mh)⁻¹) /
      ((s : ℝ) * (n ⟨t - 1, by omega⟩ : ℝ) ^ (t - k))
    let σ : ℝ := αb * (cochainDim φ Fs k : ℝ) /
      ((cochainDim φ Fs (k - 1) : ℝ) + (cochainDim φ Fs (k + 1) : ℝ))
    0 < σ ∧ IsSound σ (cssHX φ Fs β k) (cssHZ φ Fs β k) := by sorry

end GoodQLTC
