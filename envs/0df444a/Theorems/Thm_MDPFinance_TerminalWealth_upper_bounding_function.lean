-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_upper_bounding_function
-- name    : MDPFinance.TerminalWealth.upper_bounding_function
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:55:21.46461+00:00
-- url     : https://prove2.me/theorems/24cb58e1-595a-4ca9-9832-399b2f056e71
-- title:
--   Proposition 4.2.1 — $b(x)=1+x$ is an upper bounding function
-- statement:
--   $b(x) := 1+x$ is an upper bounding function for the terminal wealth Markov Decision Model.
--
--   **Formalization Note.** Two facts the book's own two-line proof cites as already established
--   are taken as hypotheses rather than re-derived: that a utility function is dominated by an
--   affine function (`hU_affine`, cited from a concavity fact used earlier in §4.1, PDF 90), and
--   that no-arbitrage forces $a\cdot\mathbb{E}R_{n+1} \leq cx$ for admissible $a$ (`ha_linear_bound`,
--   the book's own support-set argument, PDF 95). The proposition's own content — that these two
--   facts make $b=1+x$ satisfy Definition 2.4.1's three conditions — is what is proved here.
--
--   **Formalization Note (moderation).** The two facts the book's proof cites — the affine
--   upper bound on a concave utility and $a\cdot\mathbb{E}R_{n+1} \le c\,x$ for admissible $a$
--   under no arbitrage — are consequences of the model's assumptions (concavity, (FM)), not
--   hypotheses; the proposition is stated as the book states it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 80, PDF 94, Proposition 4.2.1

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Proposition 4.2.1 (Bäuerle–Rieder, p. 80, PDF 94). Under Assumption (FM) (no arbitrage, in
the model; `𝔼‖R_n‖ < ∞`, `hFM2`), the function `b(x) := 1+x` is an upper bounding function for
the Markov Decision Model: there exist `c_r, c_g, α_b ≥ 0` with (i) `r_n^+ ≤ c_r b` (trivial,
`r_n ≡ 0`); (ii) `g_N^+ = U^+ ≤ c_g b` on `E = domU`; (iii)
`𝔼[b((1+i_{n+1})(x+a·R_{n+1}))] ≤ α_b b(x)` for all `n < N`, `x ∈ E`, `a ∈ D_n(x)`. -/
theorem upper_bounding_function {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d)
    (hdomU : M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) (hFM2 : M.FM2) :
    ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ n < M.N, ∀ x ∈ M.domU, max (0 : ℝ) 0 ≤ cr * (1 + x)) ∧
      (∀ x ∈ M.domU, max (M.U x) 0 ≤ cg * (1 + x)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU, ∀ a ∈ M.D n x,
        (∫ ω, (1 + (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP) ≤
          αb * (1 + x)) := by sorry

end MDPFinance.TerminalWealth
