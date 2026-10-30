-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_apx_hardness
-- name    : NSWApxHard.Reduction.apx_hardness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:38.673213+00:00
-- url     : https://prove2.me/theorems/3697e8ea-145b-4797-ae18-5c664ad027fe
-- title:
--   §2, p. 5 — assuming Theorem 2.1, Nash social welfare is NP-hard to approximate within µ = (2(1+α)/3)^{−γ/2.5} > 1
-- statement:
--   Let $c_{\min}<c_{\max}$ be constants for which Theorem 2.1 holds: it is NP-hard to distinguish 3-regular graphs on $N$ vertices having a vertex cover of size at most $c_{\min}N$ from those all of whose vertex covers have size at least $c_{\max}N$ (Chlebík and Chlebíková prove this for $c_{\min}\approx0.5103$, $c_{\max}\approx0.5155$). Let $\alpha\in(1/3,1/2)$, $\gamma=(c_{\max}-c_{\min})/3$, and
--   $$\mu=\Big(\frac{2(1+\alpha)}{3}\Big)^{-\gamma/2.5}.$$
--   Then $\mu>1$, and it is NP-hard to approximate the Nash social welfare of indivisible items with additive utilities within factor $\mu$: it is NP-hard to distinguish inputs (agents, items, utilities, threshold $\tau$) whose optimal Nash social welfare is at least $\tau$ from inputs whose optimal Nash social welfare is at most $\tau/\mu$.
--
--   This is the paper's main result: Nash social welfare maximization is APX-hard, so the constant-factor approximation of Cole and Gkatzelis cannot be improved to an approximation scheme unless P = NP.
--
--   **Formalization Note** NP-hardness is gap NP-hardness under Karp reductions computed by Cook's one-tape Turing machines (`GapNPHard`, `CookPvsNP_defs`), from every NP language over every finite nonempty alphabet. The threshold is part of the input as a natural number $T$ with $\tau=T^{1/n}$, utilities are natural numbers, and all numbers are written in binary.
--
--   Differences from the source:
--   - reading: Theorem 2.1 of Chlebík–Chlebíková, cited and not proved in the paper → the hypothesis Theorem21 c_min c_max; reason: the paper's conclusion rests on that citation, and Lean has no proof of it.
--   - generalization: c_min ≈ 0.5103, c_max ≈ 0.5155 → any reals c_min < c_max for which Theorem 2.1 holds; reason: the page's constants satisfy c_min < c_max, and the argument uses nothing else about them.
--   - encoding: "NP-hard to approximate the Nash social welfare within factor µ" → NP-hard to distinguish "some allocation has NSW ≥ τ" from "every allocation has NSW ≤ τ/µ", with τ = T^{1/n} given in the input; reason: this is the page's completeness/soundness gap, and an algorithm approximating within any factor below µ decides it.
--   - generalization: non-negative real utilities → natural-number utilities written in binary, with n ≥ 1, n ≤ m and T ≥ 1 in both instance sets; reason: hardness on this subclass implies hardness for the paper's problem; n ≥ 1 and T ≥ 1 exclude only inputs that would be Yes- and No-instances at once.
--   - encoding: a 3-regular graph as input of Theorem 2.1 → N in binary followed by the N² adjacency bits, N ≥ 1; reason: a standard encoding, polynomially equivalent to edge lists; the empty graph is excluded because it would be a Yes- and a No-instance at once.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 5, §2 (conclusion, definition of µ; γ := (c_max − c_min)/3 on p. 5), announced on p. 1, §1; Theorem 2.1 on p. 2

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NSWApxHard_Reduction_Welfare
import Definitions.Def_NSWApxHard_Reduction_CubicVC

namespace NSWApxHard.Reduction

/-- Lee, §2, p. 5: assuming Theorem 2.1 for the constants `c_min < c_max`, for every
`α ∈ (1/3, 1/2)` the factor `μ = (2(1+α)/3)^{-γ/2.5}` with `γ = (c_max - c_min)/3` exceeds 1, and it
is NP-hard to distinguish NSW inputs whose optimum is at least `τ` from those whose optimum is at
most `τ / μ`, i.e. NP-hard to approximate the Nash social welfare within factor `μ`. -/
theorem apx_hardness (cmin cmax α : ℝ) (hc : cmin < cmax) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (hCC : Theorem21 cmin cmax) :
    1 < (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) ∧
      SetCoverThreshold.SetCover.GapNPHard encNSW nswYes
        (nswNo ((2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)))) := by sorry

end NSWApxHard.Reduction
