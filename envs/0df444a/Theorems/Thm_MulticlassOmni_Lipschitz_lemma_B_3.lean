-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_3
-- name    : MulticlassOmni.Lipschitz.lemma_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:11:58.722105+00:00
-- url     : https://prove2.me/theorems/ecd87f54-1428-43ec-9a59-855061d19fee
-- title:
--   Lemma B.3 — domain size (149), cost range (150) and validity of the mixtures $q_b(x_i)$ in the §4.1 construction
-- statement:
--   Let $C_{\mathrm{pack}}>0$ be the packing constant (in the source: that of Lemma B.2). There are constants $C_1\ge2$ and $\eta_0>0$ such that, for every integer $k\ge3$, every $0<\eta\le\eta_0$ and every Section 4.1 domain $x_1,\dots,x_N$ (`IsSection41Packing Cpack k η x`: the Lemma B.2 packing at scale $16\eta/125$, truncated to $\lfloor\eta^{-(k-2)/2}\rfloor$ points if larger):
--   1. $C_1^{-k}\eta^{-(k-2)/2}\le N\le\eta^{-(k-2)/2}$ and $N\ge128$ (149);
--   2. every cost vector of (17), $c_A$ and $c_{B_i}$ for all $i$, lies in $[1/4,3/4]^k$ (150);
--   3. the mixtures $q_b(x_i)$ of (23) with the biases (22) lie in $\Delta_k$ for every $i$ and $b\in\{0,1\}$.
--
--   Differences from the source:
--   - generalization: the construction uses the packing of Lemma B.2 with that lemma's absolute constant C_pack → the statement holds for every C_pack > 0 (∀ C_pack > 0 before the existential constants, which may depend on it); the domain is any truncation of any set satisfying Lemma B.2's conclusion at scale 16η/125 with that C_pack; reason: instantiating C_pack with Lemma B.2's constant gives the source's statement for the source's construction
--   - encoding: the domain X = {x_1, …, x_N} and functions π, θ : X → {0, 1} → an injective enumeration x : Fin N → ℝ^k and π, θ : Fin N → Fin 2 (π i is π(x_{i+1})); reason: same objects, indexed
--   - encoding: actions A, B_i with cost vectors c_A, c_{B_i} → cost x η a for a : Option (Fin N) (none = A, some i = B_i); reason: same vectors
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma B.3, p. 56

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction

namespace MulticlassOmni.Lipschitz

/-- **Lemma B.3 (Properties of the shared proper-loss construction)**, Hu, Luo, Schneider, Yang
(2026), p. 56. For the packing constant `Cpack > 0` of Lemma B.2 there are constants `C₁ ≥ 2` and
`η₀ > 0` such that for every integer `k ≥ 3`, every `0 < η ≤ η₀` and the Section 4.1 domain
`x_1, …, x_N` (the Lemma B.2 packing at scale `16η/125`, truncated to `⌊η^{-(k-2)/2}⌋` points):
`C₁^{-k} η^{-(k-2)/2} ≤ N ≤ η^{-(k-2)/2}` and `N ≥ 128` (149); every cost vector
`c_A, c_{B_i}` lies in `[1/4, 3/4]^k` (150); and `q_b(x_i) ∈ Δ_k` for all `i` and `b ∈ {0, 1}`. -/
theorem lemma_B_3 :
    ∀ Cpack : ℝ, 0 < Cpack → ∃ C₁ η₀ : ℝ, 2 ≤ C₁ ∧ 0 < η₀ ∧
      ∀ k : ℕ, 3 ≤ k → ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k η x →
          (C₁ ^ (-(k : ℝ)) * η ^ (-((k : ℝ) - 2) / 2) ≤ (N : ℝ) ∧
            (N : ℝ) ≤ η ^ (-((k : ℝ) - 2) / 2) ∧ 128 ≤ N) ∧
          (∀ (a : Option (Fin N)) (y : Fin k), cost x η a y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) ∧
          (∀ (i : Fin N) (b : Fin 2), qLip x η b i ∈ stdSimplex ℝ (Fin k)) := by sorry

end MulticlassOmni.Lipschitz
