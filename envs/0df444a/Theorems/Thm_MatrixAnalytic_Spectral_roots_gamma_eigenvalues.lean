-- Prove2me | Theorems.Thm_MatrixAnalytic_Spectral_roots_gamma_eigenvalues
-- name    : MatrixAnalytic.Spectral.roots_gamma_eigenvalues
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:09.570869+00:00
-- url     : https://prove2.me/theorems/5c0f67f8-fda9-451a-97a9-838ce1268812
-- title:
--   Theorem 9.3.1 — the roots of det(x²A₀ + x(A₁ − I) + A₂) in |z| ≤ 1 are the eigenvalues of G
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and $m$ phases, $1 \le m < \infty$. Assume that $P$ is stochastic and irreducible, that $A = A_0 + A_1 + A_2$ is irreducible, and that the QBD is positive recurrent. Let $G$ be the first-passage matrix ($G_{ij}$ the probability, starting from $(1,i)$, of reaching the level $0$ in finite time and first in $(0,j)$) and $R$ the rate matrix ($R_{ij}$ the expected number of visits to $(1,j)$ from $(0,i)$ before the first return to the level $0$). Let
--   $$\gamma(x) = \det\big(x^2A_0 + x(A_1 - I) + A_2\big).$$
--   Then:
--
--   1. $\gamma$ is not the zero polynomial;
--   2. the roots of $\gamma$ in the closed disk $|z| \le 1$, counted with multiplicity, are exactly the eigenvalues of $G$, counted with their algebraic multiplicity; in particular there are exactly $m$ of them;
--   3. the entries of $R$ are finite, and the roots of $\gamma$ with $|z| > 1$, counted with multiplicity, are at most $m$ in number and are the reciprocals $1/\eta$ of the nonzero eigenvalues $\eta$ of $R$, with the same multiplicities.
--
--   This is the goal of the mission: the eigenvalues of the probabilistic matrix $G$ (and of $R$) can be read off a polynomial in the blocks of the transition matrix, without computing $G$.
--
--   **Formalization Note** Roots are the multiset `Polynomial.roots` of $\gamma$ over $\mathbb C$, filtered by $\|z\| \le 1$ or $\|z\| > 1$; eigenvalues with multiplicity are the roots of the characteristic polynomial. $G$ and $R$ are the trajectory-sum matrices of the definition item `QBD`, read in $\mathbb C$, not arbitrary solutions of $A_0G^2 + (A_1 - I)G + A_2 = 0$ (for those the statement is false). Conclusion 1 rules out the vacuous reading in which $\gamma = 0$ has no roots. "Exactly $m$" is `Fintype.card ι`; the phase set is nonempty.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 212, Theorem 9.3.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix

namespace MatrixAnalytic.Spectral

/-- Theorem 9.3.1 (p. 212). For a positive recurrent irreducible QBD (6.1) with finitely many
phases (\`m = card ι\`) and \`A = A₀ + A₁ + A₂\` irreducible (the standing restrictions of Chapter 9,
p. 204),
the polynomial `γ(x) = det(x²A₀ + x(A₁ − I) + A₂)` is not the zero polynomial; its roots in the
closed disk `|z| ≤ 1`, counted with multiplicity, are exactly the eigenvalues of the first-passage
matrix `G` (the roots of its characteristic polynomial, with multiplicity), so there are exactly
`m` of them; and its roots with `|z| > 1` are at most `m` and are, with multiplicity, the
reciprocals of the nonzero eigenvalues of the rate matrix `R` (whose entries are finite). -/
theorem roots_gamma_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂))
    (hpos : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂)) :
    gammaPoly A₀ A₁ A₂ ≠ 0 ∧
      (gammaPoly A₀ A₁ A₂).roots.filter (fun z => ‖z‖ ≤ 1) =
        (matGc (qbdP B A₀ A₁ A₂)).charpoly.roots ∧
      Multiset.card ((gammaPoly A₀ A₁ A₂).roots.filter (fun z => ‖z‖ ≤ 1)) = Fintype.card ι ∧
      (∀ i j : ι, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      Multiset.card ((gammaPoly A₀ A₁ A₂).roots.filter (fun z => 1 < ‖z‖)) ≤ Fintype.card ι ∧
      (gammaPoly A₀ A₁ A₂).roots.filter (fun z => 1 < ‖z‖) =
        ((matRc (qbdP B A₀ A₁ A₂)).charpoly.roots.filter (fun z => z ≠ 0)).map (fun z => z⁻¹)
      := by sorry

end MatrixAnalytic.Spectral
