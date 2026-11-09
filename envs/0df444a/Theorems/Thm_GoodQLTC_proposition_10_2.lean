-- Prove2me | Theorems.Thm_GoodQLTC_proposition_10_2
-- name    : GoodQLTC.proposition_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:55:40.607971+00:00
-- url     : https://prove2.me/theorems/d8e087c4-da31-4e2e-b03f-d138d5e3deb9
-- title:
--   Proposition 10.2: binary distance and syndrome inequalities
-- statement:
--   Let $X$, $\mathcal F$ satisfy the hypotheses of Theorems 8.2 and 9.1 with $t\ge4$, $2\le k\le t-2$, $\lambda L\le1/2$, and let $Q$ be the CSS code of Equation (4.5). Put $q_k=s\,n_t^{t-k}$ and $\alpha_b=\min\{\alpha_k,\alpha'_k\}/q_k$. Then
--   $$
--   d(Q)\ge\eta\min\Big\{Z_k,\ \frac{Z_{t-k}}{M_h}\Big\},
--   $$
--   and for every $x,z\in\mathbb F_2^N$,
--   $$
--   |H_Xz|\ge\alpha_b\,\mathrm{dist}(z,\ker H_X),\qquad |H_Zx|\ge\alpha_b\,\mathrm{dist}(x,\ker H_Z). \tag{10.2}
--   $$
--
--   **Formalization Note** $M_h\ge1$ is any constant for which the two conclusions of Theorem 9.1 hold for $X$, $\mathcal F$ (in particular $M_h(t,n_t)$); $\alpha'_k=(M_h^2/\alpha_{t-k}+M_h)^{-1}$.
--
--   Differences from the source:
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
--   - generalization: M_h the constant of Theorem 9.1 → any M_h ≥ 1 for which the conclusions of Theorem 9.1 hold for this X and F; reason: the constant M_h(t, n_t) of Theorem 9.1 is such an M_h; the proof uses only those conclusions
--   - encoding: d(Q) ≥ η min{…} with d(Q) ∈ ℕ ∪ {∞} → ENNReal.ofReal(η min{…}) ≤ d(Q) in ℝ≥0∞; reason: same inequality for finite and infinite d
--   - encoding: dist(x, U) = min_{u∈U} |x − u| in an inequality → existence of a nearest u ∈ U satisfying the inequality; reason: the minimum over a finite nonempty set is attained; same instances
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
--   - encoding: an ordered F_2-basis β of F → an additive isomorphism F ≃ F_2^s; reason: the coordinate map of an ordered basis; every additive isomorphism of F_2-spaces is F_2-linear
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Proposition 10.2, pp.31–32 (PDF pp.34–35)

import Mathlib
import Definitions.Def_GoodQLTC_cssDist
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

/-- **Proposition 10.2** (binary distance and syndrome inequalities), Gay–Jeronimo,
arXiv:2609.20780 (held version), pp.31–32: let `X` and `F` satisfy the hypotheses of Theorems 8.2
and 9.1, with `t ≥ 4`, `2 ≤ k ≤ t − 2` and `λL ≤ 1/2`, and let `Q` be the CSS code of Equation
(4.5). With `q_k := s n_t^{t−k}` and `α_b := min{α_k, α'_k}/q_k`, the code satisfies
`d(Q) ≥ η min{Z_k, Z_{t−k}/M_h}`, and for every `x, z ∈ F_2^N`,
`|H_X z| ≥ α_b dist(z, ker H_X)` and `|H_Z x| ≥ α_b dist(x, ker H_Z)` (10.2).

**Formalization Note.** `M_h ≥ 1` is the constant of Theorem 9.1: the statement holds for every
`M_h ≥ 1` for which the two conclusions of Theorem 9.1 hold for this `X` and `F` (hypotheses
`hsys`, `hcyc`), in particular for `M_h(t, n_t)`; `α'_k := (M_h²/α_{t−k} + M_h)^{−1}`. Both product-expansion hypotheses
(primal for Theorem 8.2, dual for Theorem 9.1) are assumed, together with the standing
assumptions of §§8–9. `β` is any ordered `F_2`-basis of `F` (stalk bases are the coordinates).
Weights are binary Hamming weights; `d(Q) ∈ ℕ∞` is compared through `ENNReal.ofReal`; `dist` is
attained, so (10.2) is stated as the existence of a nearest kernel vector. -/
theorem proposition_10_2 {t : ℕ} (ht : 4 ≤ t) {X : Type} [PartialOrder X] [Fintype X]
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
    ENNReal.ofReal (etaConst t ρ τ * min (numFaces φ k : ℝ) ((numFaces φ (t - k) : ℝ) / Mh)) ≤
        ((cssDist (cssHX φ Fs β k) (cssHZ φ Fs β k) : ℕ∞) : ENNReal) ∧
    (∀ z, ∃ y, (cssHX φ Fs β k).mulVec y = 0 ∧
      αb * (hammingNorm (z - y) : ℝ) ≤ (hammingNorm ((cssHX φ Fs β k).mulVec z) : ℝ)) ∧
    (∀ x, ∃ y, (cssHZ φ Fs β k).mulVec y = 0 ∧
      αb * (hammingNorm (x - y) : ℝ) ≤ (hammingNorm ((cssHZ φ Fs β k).mulVec x) : ℝ)) := by sorry

end GoodQLTC
