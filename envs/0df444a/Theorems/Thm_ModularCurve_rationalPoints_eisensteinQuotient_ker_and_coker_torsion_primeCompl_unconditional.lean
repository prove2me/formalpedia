-- Prove2me | Theorems.Thm_ModularCurve_rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional
-- name    : ModularCurve.rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/ed4bed32-952b-5f5f-86df-84699e57a31d
-- title:
--   Rational points versus Eisenstein quotient: kernel and cokernel torsion
-- statement:
--   Let $p$ be a nonzero natural number (primality of $p$ is not assumed) and let $q$ be a prime. Write $J =$ `JZero p` for the degree-zero divisor class group $\mathrm{Pic}^0$ of the field `modularFunctionFieldBar p` over $\overline{\mathbb{Q}}$, equipped with the action of the Hecke algebra $\mathbb{T} =$ `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ supplied by `heckeModuleBar p` (the action through `heckeEvalBar` when the bar Hecke operators commute, and the trivial action otherwise), and with the natural action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}}$. Let $K \subseteq J$ be `eisensteinKernelSubmodule p`, namely the submodule `eisensteinKernel (JZero p) (eisensteinIdeal p)` $\cdot\, J$ obtained by letting that ideal of $\mathbb{T}$ act on all of $J$, let $\tilde J = J/K$ with quotient map $[\,\cdot\,] =$ `eisensteinQuotientMk p`, and let $\mathfrak{P} =$ `eisensteinMaximalIdeal p q` be the preimage under `eisensteinEval p` $=$ `MvPolynomial.aeval (eisensteinSystem p)` of the ideal $(q) \subseteq \mathbb{Z}$, so $s \notin \mathfrak{P}$ means $q \nmid$ `eisensteinEval p` $s$. The assertion is the conjunction of two statements. First: for every $x \in J$ fixed by every element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with $[x] = 0$, there exists $s \in \mathbb{T}$ with $s \notin \mathfrak{P}$ and $s \cdot x = 0$. Second: for every $z$ in the $\mathbb{T}$-span of `eisensteinQuotientRational p`, the set of classes $[x]$ with $\sigma \cdot x - x \in K$ for all $\sigma$, there exist $s \notin \mathfrak{P}$ and a Galois-fixed $x \in J$ with $s \cdot z = [x]$.
--
--   This is the elementwise form of Mazur's comparison, in Modular curves and the Eisenstein ideal III §3, between the rational points of $J_0(p)$ and the $\mathbb{T}$-span of the rational part of the Eisenstein quotient: after localisation at the Eisenstein maximal ideal of residue characteristic $q$ the natural map has trivial kernel and cokernel, expressed here by witnesses $s \notin \mathfrak{P}$ rather than by localised modules. It feeds the statement about sections of the identity component of the Néron model of $J_0(p)$, where it is combined with finite index of those sections in $J(\mathbb{Q})$ and exactness of localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal
import Definitions.Def_ModularCurve_MazurStepThreeInputs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.rationalPoints_eisensteinQuotient_ker_and_coker_torsion_primeCompl_unconditional
    (p : ℕ) [NeZero p] (q : ℕ) [Fact q.Prime] :
    letI := heckeModuleBar p
    (∀ x : JZero p, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) →
        eisensteinQuotientMk p (heckeModuleBar p) x = 0 →
        ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ s • x = 0) ∧
    (∀ z ∈ Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)),
        ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧
          ∃ x : JZero p, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • x = x) ∧
            s • z = eisensteinQuotientMk p (heckeModuleBar p) x) := by sorry
