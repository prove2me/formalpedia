-- Prove2me | Theorems.Thm_OPG37364_lps13_eigenspace_finrank_lower_bound
-- name    : OPG37364.lps13_eigenspace_finrank_lower_bound
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-10T10:18:54.113311+00:00
-- url     : https://prove2.me/theorems/9664d382-ca66-4fcf-a0d7-cd5e86dc95f2
-- title:
--   Multiplicity lower bound for nontrivial LPS13 adjacency eigenvalues
-- statement:
--   Let q>13 be prime, choose i in the finite field F_q with i²=-1, and suppose 13 is a quadratic nonresidue modulo q. Let A be the ordinary, unnormalized complex adjacency operator of the existing fixed-p=13 LPS graph on PGL₂(F_q). For a real number μ with μ≠14 and μ≠−14, suppose the complex eigenspace E_μ=ker(A−μI) is nonzero. Then
--
--   q−1 ≤ 2 dim_ℂ(E_μ).
--
--   The proof first shows that the existing PSL₂(F_q) left-translation representation on E_μ is nontrivial, then applies the already-proved Frobenius representation-degree lower bound. The nonzero-eigenspace hypothesis is explicit and is not merely nonemptiness. No connectedness, girth, spectral estimate, or graph-existence assumption is used. This is the fixed-p=13 nonsquare-determinant specialization of the multiplicity argument in DSV Proposition 4.4.3; it is not a formalization of the subsequent weak spectral estimate.
-- source:
--   Davidoff–Sarnak–Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs (2003), Proposition 4.4.3 and its proof, printed pp. 124–125, specialized to p=13 and the quadratic-nonresidue/PGL case. It applies the classical Frobenius lower bound of Theorem 3.5.1. https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . This formalizes classical mathematics; no novelty or LPS existence/spectral-bound claim is made.

import Definitions.Def_opg37364_lps13_eigenspaces
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false

namespace OPG37364

theorem lps13_eigenspace_finrank_lower_bound
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ) (hμ14 : μ ≠ 14) (hμneg14 : μ ≠ -14)
    (hE : Nontrivial (lps13AdjacencyEigenspace hq i μ)) :
    q - 1 ≤ 2 * Module.finrank ℂ (lps13AdjacencyEigenspace hq i μ) := by sorry

end OPG37364
