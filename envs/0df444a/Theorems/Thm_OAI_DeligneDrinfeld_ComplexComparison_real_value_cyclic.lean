-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_ComplexComparison_real_value_cyclic
-- name    : OAI.DeligneDrinfeld.ComplexComparison.real_value_cyclic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:45:37.391227+00:00
-- url     : https://prove2.me/theorems/3bcfb825-a994-439d-84c8-9b6c4691bf9c
-- title:
--   Section 7 (OpenAI, Deligne–Drinfeld) — the truncated KZ comparison value satisfies the three-term (hexagon) relation
-- statement:
--   For $N \in \mathbb N$ let $Q_N$ be the free associative real algebra on $X, Y$ truncated above length $N$ (`CutoffDepth.Q ℝ N`), and let $\rho_N$ be its algebra automorphism $X \mapsto Y$, $Y \mapsto -X - Y$ (`ComplexComparison.realRotate N`). Let $v_N \in Q_N$ be OpenAI's KZ comparison value (`KZComparison.value N`): from the two normalized solutions $G_0 = (\tfrac12)^X\,\mathcal T_N[\Omega_0](\tfrac12)$ and $G_1$ (the same with $X$ and $Y$ exchanged) of the truncated transport equation with $\Omega_0(s) = s^{-X}\frac{1}{s-1}Y s^{X}$, put $P = G_1^{-1}G_0$ and let $V$ be its sign-flipped version (each word of length $k$ multiplied by $(-1)^k$), form the automorphism $\theta = \tau_V \circ \tau_P^{-1}$ of $Q_N$ and the element $A = V\,\theta(P)^{-1}$; then $v_N$ is the operator logarithm $\log(1 + T)$, with $T(a) = A\,\theta(a) - a$, applied to $1$ and truncated after $T^{N+1}$. The statement is
--
--   $$\forall N:\quad v_N + \rho_N(v_N) + \rho_N(\rho_N(v_N)) = 0 \quad \text{in } Q_N.$$
--
--   The construction and its conventions (iterated integrals with $\Omega$ multiplying on the left, $s^a = \exp(a \log s)$, inverses of units) are OpenAI's definitions in the bundles `Def_DeligneDrinfeldInternals` and `Def_DeligneDrinfeldKZ`.
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), §7, pp. 31–38: the operator logarithm $\delta = \log S$ of the comparison $S = H_- H_+^{-1}$ of the two holonomy functors (7.10) is “a compatible derivation and coderivation” (p. 36), and the values $\delta_n(\alpha)$ lie in $V_n \subseteq W_n$ (Proposition 6.1, p. 28), so they satisfy the three-term relation (1.3), “$\psi(x, y) + \psi(y, -x-y) + \psi(-x-y, x) = 0$” (p. 2). This statement is OpenAI's Lean theorem `OAI.DeligneDrinfeld.ComplexComparison.real_value_cyclic` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), that relation for the real truncated value in the associative envelope. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Section 7, pp. 31-38, with the three-term relation (1.3), p. 2; Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldKZ

namespace OAI.DeligneDrinfeld.ComplexComparison

theorem real_value_cyclic (N : ℕ) :
    OAI.DeligneDrinfeld.KZComparison.value N +
          (OAI.DeligneDrinfeld.ComplexComparison.realRotate N) (OAI.DeligneDrinfeld.KZComparison.value N) +
        (OAI.DeligneDrinfeld.ComplexComparison.realRotate N)
          ((OAI.DeligneDrinfeld.ComplexComparison.realRotate N) (OAI.DeligneDrinfeld.KZComparison.value N)) =
      0 := by
  sorry

end OAI.DeligneDrinfeld.ComplexComparison
