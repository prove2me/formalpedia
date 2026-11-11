-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_60
-- name    : MultiCorrectPAC.Demo.theorem_60
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:48.671182+00:00
-- url     : https://prove2.me/theorems/e218ab1b-07a8-4f8d-aa7e-c5751c9e5e3f
-- title:
--   Theorem 60 — d∩_pack,ρ(I_{ℓ+1}(H)) ≤ c d log(d + 2) for d = d∩_DS(I_{ℓ+1}(H)) or d_pair(I_{ℓ+1}(H))
-- statement:
--   Let $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$ be nonempty and fix $0<\rho\le1$. Let $d$ be either $d^\cap_{\mathrm{DS}}(\mathcal I_{\ell+1}(\mathcal H))$ or $d_{\mathrm{pair}}(\mathcal I_{\ell+1}(\mathcal H))$. There is a constant $c$ depending only on $\ell$ and $\rho$ such that, if $d<\infty$,
--   $$d^\cap_{\mathrm{pack},\rho}(\mathcal I_{\ell+1}(\mathcal H))\le c\,d\log(d+2).\tag{82}$$
--   The bound holds for arbitrary sets $\mathcal X$ and $\mathcal Y$, countable or not.
--
--   For intersection classes the DS-type dimensions control the packed dimension, which gives (iv) ⇒ (vi) and (v) ⇒ (vi) in Theorem 41.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: I_R(H) of (7): g = ⋂ₐ hₐ on any B ⊆ ⋂ₐ supp(hₐ) where the intersection is nonempty, ⋆ off B, 1 ≤ r ≤ R → interClass R H: ∃ r ∈ [1, R], hs : Fin r → H with g x = none or g x = some A, A nonempty, A = {y : ∀ a, y ∈ hs a x}; reason: B is supp(g); nonemptiness of the intersection forces every hₐ to be defined on B
--   - encoding: a constant c depending only on ℓ and ρ → ∃ c : ℝ, 0 < c placed after ∀ ℓ and ρ and before ∀ X Y H (and all ε, δ, m, d); reason: the quantifier order that makes c independent of X, Y, k, H, d, m, ε, δ
--   - encoding: arbitrary sets X and Y → X Y : Type with no instance arguments; reason: Lean convention
--   - encoding: d∩_pack,ρ(I_{ℓ+1}(H)) ≤ c d log(d+2) → ∃ p : ℕ, packDim ℓ ρ (interClass (ℓ+1) H) = p ∧ (p : ℝ) ≤ c * d * Real.log (d + 2); reason: the bound forces the packed dimension to be finite
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 81 (PDF 83), Theorem 60, (82)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_60 :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (X Y : Type) (H : Set (Hyp X Y)), IsClass ℓ H → H.Nonempty →
      ∀ d : ℕ, (dsDim (interClass (ℓ + 1) H) = d ∨ pairDim (interClass (ℓ + 1) H) = d) →
        ∃ p : ℕ, packDim ℓ ρ (interClass (ℓ + 1) H) = p ∧
          (p : ℝ) ≤ c * d * Real.log ((d : ℝ) + 2) := by sorry

end MultiCorrectPAC.Demo
