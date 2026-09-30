-- Prove2me | Theorems.Thm_IntroBandits_bic_never_explores_without_property
-- name    : IntroBandits.bic_never_explores_without_property
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:36:44.89938+00:00
-- url     : https://prove2.me/theorems/6bf06dc6-541a-49ca-861f-ecae1118e57d
-- title:
--   Theorem 11.19: absent Property (11.12), any BIC algorithm (ties to arm 1) never plays arm 2
-- statement:
--   **Theorem 11.19.** Suppose ties in Definition 11.4 are always resolved in favor of arm 1 (i.e., imply $\mathrm{rec}_t = 1$). Absent (11.12), any BIC algorithm never plays arm 2.
--
--   Formally: $P$ a prior supported on the finite $F \subseteq [0,1]^2$, any reward family; suppose Property (11.12) fails, i.e. for every $n$ and every tuple $s$ of $n$ samples of arm 1, $\mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{S_{1,n} = s\}] \le 0$ (so $\Pr[G_{1,n} > 0] = 0$ for every $n$). Let $\pi$ be a bandit policy over $T$ rounds that is BIC with the tie convention: BIC, and whenever $\Pr[\mathrm{rec}_t = 2] > 0$, $\mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{\mathrm{rec}_t = 2\}] > 0$ (arm 2 is recommended only when strictly better). Then for every round $t$, $\Pr[\mathrm{rec}_t = 2] = 0$ under the joint law of the compliant run. "Never plays" is "with probability zero", which is what the induction of the proof establishes.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.5 p. 153, Theorem 11.19 with its proof by induction

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem bic_never_explores_without_property (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    (hno : ¬ PriorAllowsExploration P F fam) {T : ℕ} {π : BanditPolicy 2}
    (hπ : IsStrictlyBIC F (jointMeasure P F fam π T) (fun h t ↦ (h t).1)) :
    ∀ t : Fin T, jointMeasure P F fam π T (Set.univ ×ˢ {h | (h t).1 = 1}) = 0 := by sorry

end IntroBandits
