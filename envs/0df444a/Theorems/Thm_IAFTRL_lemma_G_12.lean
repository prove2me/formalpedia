-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_12
-- name    : IAFTRL.lemma_G_12
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:18:27.569644+00:00
-- url     : https://prove2.me/theorems/0cd99021-119f-4fa9-b3d2-f0df0b624035
-- title:
--   Lemma G.12 — every sharp optimal action is a reference atom
-- statement:
--   **Setting.**
--   - $\mathcal A\subseteq\mathbb B^d$ is compact and spanning, and $\mathcal B$ is a compact generator of it.
--   - $e$ is a surjective enumeration of $\mathbb Q^d$. The candidate $b_m$ is the lexicographically least minimizer of $a\mapsto a^\top e(m)$ on $\mathcal B$, and $J$ is the set of first occurrences.
--   - $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$. Sharpness holds: $\varsigma\|a-a^*\|_{\mathcal S}\le(a-a^*)^\top\theta$ on $\mathrm{Conv}\,\mathcal A$ for some $\varsigma>0$.
--
--   **Claim.** There is $m\in J$ with $b_m=a^*$. Hence $a^*$ is an atom of the reference measure $\mu$, with $\mu(\{a^*\})\ge\pi_m>0$.
--
--   **Proof idea.**
--   1. Every $\vartheta$ with $\|\vartheta-\theta\|_{\mathcal A}\le\varsigma/2$ keeps $a^*$ as the unique minimizer on $\mathcal K$, by duality $|x^\top z|\le\|x\|_{\mathcal S}\|z\|_{\mathcal A}$.
--   2. Such a $\vartheta$ can be chosen rational.
--   3. The enumeration reaches it, the lexicographic selection then picks $a^*$, and the first occurrence lies in $J$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6.2, Lemma G.12, pp. 144–145

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.12 (Every sharp optimal action is a reference atom).** Zhao–Tan, *Best-of-Both-Worlds
FTRL for Linear Bandits* (STOC submission version), Lemma G.12, p.144: "Suppose a parameter has a
unique optimal action `a*` and `ς = inf_{a∈𝒦\{a*}} (a − a*)ᵀθ / ‖a − a*‖_𝒮 > 0`. Then `a* = b_{j*}`
for some finite index `j*`."

For a compact generator `ℬ` of a compact spanning action set `𝒜 ⊆ 𝔹^d`, a surjective enumeration
`e` of `ℚ^d`, and a sharp instance with unique optimal action `a* ∈ 𝒜`, the optimal action is the
candidate `cand ℬ e m` of some first-occurrence index `m ∈ J`; in particular it is an atom of the
reference measure (3.3). -/
theorem lemma_G_12 {d : ℕ} (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) (hsharp : IsSharp 𝒜 θ astar) :
    ∃ m ∈ Jset ℬ e, cand ℬ e m = astar := by sorry

end IAFTRL
