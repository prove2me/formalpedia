-- Prove2me | Theorems.Thm_GoodQLTC_theorem_8_2
-- name    : GoodQLTC.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:55:04.080569+00:00
-- url     : https://prove2.me/theorems/ec9b9a85-5a0f-477b-b37b-b53ed8ff6110
-- title:
--   Theorem 8.2: cosystolic distance and cocycle expansion
-- statement:
--   In the setting of §8 ($t\ge2$, $0<\rho\le1$, $\tau\ge1$, $X$ regular $\lambda$-expanding with $n_t/n_1\le\tau$, $\mathcal F$ an $\mathbb F_{2^s}$-cosheaf with compatible base codes whose local families $\{C_{f,i}\}_{i\in I}$ are universally $\rho$-product-expanding), suppose $\lambda L\le1/2$. Then:
--   1. for $1\le j<t$, every nonzero locally minimal cocycle in $C^j$ has block weight at least $\eta Z_j$;
--   2. for $1\le j<t$, every representative of a nonzero class in $H^j(X;\mathcal F)$ has block weight at least $\eta Z_j$;
--   3. for $1\le j\le t-2$ and every $x\in C^j$,
--   $$
--   |\delta^jx|_b\ge\alpha_j\,\mathrm{dist}_b(x,\ker\delta^j).
--   $$
--   Here $L$, $\eta$, $\alpha_j$ are the explicit constants of §8.
--
--   Differences from the source:
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
--   - encoding: dist(x, U) = min_{u∈U} |x − u| in an inequality → existence of a nearest u ∈ U satisfying the inequality; reason: the minimum over a finite nonempty set is attained; same instances
--   - encoding: representative of a nonzero class in H^j → a cocycle not in the image of δ^{j−1}; reason: definition of a nonzero cohomology class
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 8.2, p.25 (PDF p.28); Definition 8.1 and constants, p.25

import Mathlib
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_IsExpanding
import Definitions.Def_GoodQLTC_BaseCodeData
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_cobdMat
import Definitions.Def_GoodQLTC_IsLocallyMinimal
import Definitions.Def_GoodQLTC_etaConst

namespace GoodQLTC

universe u

/-- **Theorem 8.2** (cosystolic distance and cocycle expansion), Gay–Jeronimo, arXiv:2609.20780
(held version), p.25: suppose `λL ≤ 1/2`. For `1 ≤ j < t`, every nonzero locally minimal cocycle
in `C^j` and every representative of a nonzero class in `H^j(X; F)` have block weight at least
`η Z_j`. For `1 ≤ j ≤ t − 2` and every `x ∈ C^j`, `|δ^j x|_b ≥ α_j dist_b(x, ker δ^j)`, where
`α_j := min{1/sym_j(n_1,…,n_t), η sym_{j+1}(n_1,…,n_t)/(2 sym_j(n_1,…,n_t))}`.

**Formalization Note.** Standing assumptions of §8 (p.25): `t ≥ 2`, `0 < ρ ≤ 1`, `τ ≥ 1`, `X` a
regular, `λ`-expanding `t`-dimensional cubical complex with degrees `2 ≤ n_1 ≤ ⋯ ≤ n_t`,
`n_t/n_1 ≤ τ`, `F` a cosheaf over `F = F_{2^s}` with compatible base codes `D` (`0 < m_{i,b} <
n_i`) whose local families `{C_{f,i}}_{i∈I}` are universally `ρ`-product-expanding. `L`, `η`,
`α_j` are the explicit constants of p.25 (with `C_mix` of p.24). A representative of a nonzero
class is a cocycle not in `im δ^{j−1}`; `dist_b(x, ker δ^j)` is attained, so the last bound is an
existence of a nearest cocycle `y`. -/
theorem theorem_8_2 {t : ℕ} (ht : 2 ≤ t) {X : Type} [PartialOrder X] [Fintype X]
    {φ : X → Fin t → Option Bool} {n : Fin t → ℕ} (hn : ∀ i, 2 ≤ n i) (hmono : Monotone n)
    (hX : IsCubicalComplex t φ) (hreg : IsRegular φ n) (lam : ℝ) (hexp : IsExpanding φ n lam)
    {F : Type} [Field F] [Fintype F] {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ s)
    (Fs : Cosheaf X F) {m : Fin t → Bool → ℕ} (hm : ∀ i b, 0 < m i b ∧ m i b < n i)
    (D : BaseCodeData φ Fs m) (hD : IsCompatible D)
    (ρ τ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 1 ≤ τ)
    (hratio : (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ)
    (hPE : ∀ (f : X) (I : Finset (Fin t)), I.Nonempty → I ⊆ codir φ f →
      IsUnivProductExpanding.{u} ρ (fun i : I => localCode D f i.1))
    (hlamL : lam * LConst t ρ τ ≤ 1 / 2) :
    (∀ j : ℕ, 1 ≤ j → j < t → ∀ x : Cochain φ Fs j F, x ≠ 0 →
      (cobdMat φ Fs j (j + 1)).mulVec x = 0 → IsLocallyMinimal φ Fs j x →
      etaConst t ρ τ * (numFaces φ j : ℝ) ≤ (blockWeight x : ℝ)) ∧
    (∀ j : ℕ, 1 ≤ j → j < t → ∀ x : Cochain φ Fs j F,
      (cobdMat φ Fs j (j + 1)).mulVec x = 0 →
      x ∉ LinearMap.range (cobdMat φ Fs (j - 1) j).mulVecLin →
      etaConst t ρ τ * (numFaces φ j : ℝ) ≤ (blockWeight x : ℝ)) ∧
    (∀ j : ℕ, 1 ≤ j → j + 2 ≤ t → ∀ x : Cochain φ Fs j F,
      ∃ y : Cochain φ Fs j F, (cobdMat φ Fs j (j + 1)).mulVec y = 0 ∧
        alphaConst n ρ τ j * (blockWeight (x - y) : ℝ) ≤
          (blockWeight ((cobdMat φ Fs j (j + 1)).mulVec x) : ℝ)) := by sorry

end GoodQLTC
