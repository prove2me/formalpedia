-- Prove2me | Theorems.Thm_ModularCurve_exists_toricDichotomyData_jZero
-- name    : ModularCurve.exists_toricDichotomyData_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/1092ddc4-3d07-587b-b24a-0b5a9da97f2f
-- title:
--   Toric data and 𝔪-dichotomy for J₀(Nq) at q
-- statement:
--   Let $N,q$ be nonzero natural numbers with $q$ prime and $q\nmid N$. Assume the project's input packages: [`ModularCurve.HeckeInputsAll`](def/ModularCurve_HeckeInputsAll.html#L8) at levels $Nq$ and $N$ (for every prime $\ell$, the integrality of the two degeneracy embeddings, the existence of principal divisors, finiteness, the fundamental identity and the pushforward norm formula needed to define the $\ell$-th Hecke correspondence on the degree-zero divisor class group of the base-changed modular function field over $\overline{\mathbb Q}$), `HeckeOperatorsCommuteBar` at both levels (the operators `heckeOperatorBar` commute pairwise), and `DegeneracyPushforwardInputs N q` (integrality, finiteness and norm formulas for the maps `heckeAlphaBar` and `heckeBetaBar`, which make the two degeneracy pushforwards $J_0(Nq)\to J_0(N)$ defined). Then there exist a finite set $S$ of primes, a subgroup $I$ of $\overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$, an element $\mathrm{frob}$ of that group, and a valuation subring $A$ of $\overline{\mathbb Q}$ such that: every $\ell\in S$ divides $Nq$; $q\in S$; $q$ is a non-unit of $A$ (`LiesOverPrime`); $\mathrm{frob}$ lies in the decomposition subgroup of $A$ and acts as $x\mapsto x^{q}$ on the residue field of $A$ (`IsFrobeniusAt`); $I$ is contained in the inertia subgroup of $A$ over $\mathbb Q$; and, with $J=J_0(Nq)$ and $J_0=J_0(N)$ taken to be the groups [`ModularCurve.JZero`](def/ModularCurve_ArithmeticGalois.html#L115) (degree-zero divisor class groups of `modularFunctionFieldBar` over $\overline{\mathbb Q}$) equipped with the `heckeModuleBar` module structures over $\mathbb T=\mathbb Z[T_\ell:\ell\text{ prime}]=$ `HeckeAlg`, the predicate `ExistsToricDichotomyDataQGuarded` holds for $(J,q,S,I,\mathrm{frob},J_0)$. Unfolded, the last clause says: there is a $\mathbb T$-submodule $\mathcal T\subseteq J$ with (i) $\mathrm{frob}\cdot(\mathrm{frob}\cdot x)=q^{2}x$ for all $x\in\mathcal T$, (ii) $\mathrm{frob}\cdot x=(q\,T_q)\cdot x$ for all $x\in\mathcal T$, where $T_q=$ `heckeGen q`, and (iii) for every maximal ideal $\mathfrak m\subset\mathbb T$ that is not eventually Eisenstein (i.e. there is no finite set outside which $T_\ell-(\ell+1)\in\mathfrak m$) and for which $q$ is a unit in $\mathbb T/\mathfrak m$, every $x\in J$ annihilated by $\mathfrak m$ and fixed by all $\sigma\in I$ either lies in $\mathcal T$ or else `HasLowerLevelTorsion S 𝔪 J₀` holds, namely there is a non-zero $y\in J_0$ killed by every integer in $\mathfrak m$ and by every $T_\ell-b$ ($\ell\notin S$, $b\in\mathbb Z$) lying in $\mathfrak m$. Note that `heckeModuleBar` is defined by a case split: when the Hecke operators commute, `heckeGen` $\ell$ acts as `heckeOperatorBar` $\ell$, and otherwise all generators act by zero; the commutation hypotheses put the first branch in force, but the conclusion does not itself record this link.
--
--   This is the geometric input at the auxiliary prime $q$ in Ribet's level-lowering argument (Mazur's principle): the toric part of $J_0(Nq)$ at $q$, on which Frobenius squares to $q^2$ and equals $qT_q$, together with the dichotomy that a non-Eisenstein $\mathfrak m$-torsion class invariant under inertia at $q$ either lies in the toric part or produces torsion at level $N$. The formal statement is phrased entirely in terms of the project's abstract predicates — no Néron model, special fibre or component group appears — and its lower-level alternative is an abstract non-vanishing statement about $J_0(N)$ rather than a statement about the images under the two degeneracy pushforwards, so it is shaped differently from both the textbook result and the project's abelian-part predicate `IsAbelianPartData`; the set $S$, the inertia subgroup $I$ (only required to be contained in the inertia subgroup of $A$), the Frobenius element and the place $A$ are all produced existentially. It is used in the two theorems lowering the level of residual modularity from $M$ to $M/q$ for a prime $q$ exactly dividing a squarefree $M$ at which the residual representation is unramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_toricDichotomyData_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_ToricDichotomyData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_toricDichotomyData_jZero (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hinNq : ModularCurve.HeckeInputsAll (N * q)) (hcommNq : ModularCurve.HeckeOperatorsCommuteBar (N * q))
    (hinN : ModularCurve.HeckeInputsAll N) (hcommN : ModularCurve.HeckeOperatorsCommuteBar N)
    (hdeg : ModularCurve.DegeneracyPushforwardInputs N q) :
    ∃ (S : Finset Nat.Primes) (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (A : ValuationSubring (AlgebraicClosure ℚ)),
      (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q) ∧ (⟨q, hq⟩ : Nat.Primes) ∈ S ∧ A.LiesOverPrime q ∧ A.IsFrobeniusAt frob q ∧ I ≤ A.inertiaSubgroupIn ℚ ∧
      (letI := ModularCurve.heckeModuleBar (N * q)
       letI := ModularCurve.heckeModuleBar N
       ModularCurve.ExistsToricDichotomyDataQGuarded (ModularCurve.JZero (N * q)) ⟨q, hq⟩ S I frob (ModularCurve.JZero N)) := by sorry
