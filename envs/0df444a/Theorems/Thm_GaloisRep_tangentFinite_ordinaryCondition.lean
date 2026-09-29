-- Prove2me | Theorems.Thm_GaloisRep_tangentFinite_ordinaryCondition
-- name    : GaloisRep.tangentFinite_ordinaryCondition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/7e739142-a40d-5ca5-b8f2-1b14e94cbdfb
-- title:
--   Finiteness of the ordinary-condition tangent space
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field $k = \mathrm{ResidueField}\,\mathcal{O}$ is finite, let $\bar\rho$ be a residual Galois representation over $k$ (in the project's sense: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\,\mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\,\mathbb{Q}$ to $\mathrm{End}_k V$ satisfying the project's condition [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17)), let $p$ be a natural number and let $S$ be a finite set of natural numbers. The theorem asserts `TangentFinite 𝒪 ρbar (ordinaryCondition 𝒪 p S)`, which by definition says the following. Give the dual numbers $k[\varepsilon]$ the $\mathcal{O}$-algebra structure obtained by composing $\mathcal{O} \to k$ with $k \to k[\varepsilon]$, and $\mathrm{ResidueField}\,k[\varepsilon]$ the $k$-algebra structure obtained from $k \to k[\varepsilon] \to \mathrm{ResidueField}\,k[\varepsilon]$; then the set of those $\rho \in$ [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) $k[\varepsilon]$ which satisfy `ordinaryCondition 𝒪 p S` and whose residual representation is equivalent to the base change of $\bar\rho$ to $\mathrm{ResidueField}\,k[\varepsilon]$, taken modulo the equivalence of [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16)s, is a finite set. Here `ordinaryCondition 𝒪 p S ρ` is the conjunction of three project-defined clauses: $\rho$ has cyclotomic determinant at $p$ (`DetIsCyclotomic`), $\rho$ is ordinary at $p$ (`IsOrdinaryAt`, existence of a free rank-one submodule spanned by a basis vector, stable under each decomposition subgroup above $p$ and containing $(\rho(\sigma) - 1)V$ for $\sigma$ in the corresponding inertia subgroup), and $\rho$ is unramified at every prime $q \notin S$. Note that $p$ is not assumed prime and $S$ is not assumed to consist of primes, so for degenerate $p$ the asserted finiteness is about a possibly degenerate condition.
--
--   This is the finiteness of the tangent space of the ordinary deformation problem, i.e. the finiteness of the set of deformations of $\bar\rho$ to the dual numbers satisfying the ordinary condition, in the sense of Mazur's formulation of deformation theory and of Wiles's ordinary deformation problem. Unlike the textbook statement, nothing here is said about the tangent space being a finite-dimensional $k$-vector space or about its identification with a Selmer or cohomology group: only finiteness of the quotient set is asserted, and no hypothesis is imposed on $p$, on $S$, or on $\bar\rho$ (no irreducibility, and no assumption that $\bar\rho$ itself is ordinary). It supplies the tangent-finiteness hypothesis of the project's representability theorem in the ordinary case, and is used in the construction of ordinary deformation-ring data for residual representations and, via that, for the residual representations attached to semistable Weierstrass models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_tangentFinite_ordinaryCondition.lean

import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem GaloisRep.tangentFinite_ordinaryCondition (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (p : ℕ) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar (ordinaryCondition 𝒪 p S) := by sorry
