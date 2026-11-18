-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_ref_id
-- name    : IAFTRL.lemma_G_ref_id
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T15:58:27.746694+00:00
-- url     : https://prove2.me/theorems/6745639f-3366-4706-be93-d092f6605651
-- title:
--   Reference identification for GIA-FTRL on Laplace histories
-- statement:
--   **Setting.** The sharp instance of Proposition 3.1. Here $\mathcal A$ is a compact action set in the unit ball spanning $\mathbb R^d$, and $\mathcal B$ is a compact generator. The enumeration $e$ is surjective, $a^*$ is the unique optimal action, the instance is sharp, and $\Delta(a)=(a-a^*)^\top\theta$. GIA-FTRL chooses at round $n$ the reference action $b_{r_n}$ of (3.4), where $r_n$ is the least index $j\in J$ minimizing $b_j^\top S+\beta_nh_j$ over the candidate atoms $b_j$ with reinforced priorities $h_j$ of (3.2).
--
--   **Claim.** There is a round $T_r$, depending only on the instance, such that the following holds for every $n\ge T_r$ and every $S\in\mathbb R^d$. If
--   $$(a-a^*)^\top S\ \ge\ 4n^{7/8}\Delta(a)\qquad\text{for all }a\in\mathcal K,$$
--   then the reference action is $b_{r_n}=a^*$.
--
--   **Formalization Note.** This is the deterministic part of the statement "on $G_t^{\rm cor}$ the reference is $a^*$" in Lemma G.26. The Laplace lower bound of (G.554) holds on $G_t^{\rm cor}$, and the claim shows that this bound alone forces the reference to be $a^*$ for large $n$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6, Lemma G.26 ("On G_t^cor the reference is a*"), with the reference rule (3.4) and priorities (3.2)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Reference identification on Laplace histories.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.26, p.174: "On `G_t^cor` the reference is
`a*`", with the reference index (3.4) `r_t = argmin_{j∈J} {b_jᵀ L̂_{t−1} + β_t h_j}` and the
reinforced priorities (3.2).

Deterministic form: in the sharp setting there is a round `T_r` such that for every round
`n ≥ T_r` and every cumulative estimate `S` with `(a − a*)ᵀS ≥ 4 n^{7/8} Δ(a)` on `𝒦`, the
reference action of program (3.6) is `b_{r_n} = a*`. -/
theorem lemma_G_ref_id {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ Tr : ℕ, ∀ (n : ℕ) (S : Fin d → ℝ), Tr ≤ n →
      (∀ a ∈ Kset ℬ, 4 * (n : ℝ) ^ ((7 : ℝ) / 8) * ((a - astar) ⬝ᵥ θ) ≤ (a - astar) ⬝ᵥ S) →
      gref ℬ e n S = astar := by sorry

end IAFTRL
