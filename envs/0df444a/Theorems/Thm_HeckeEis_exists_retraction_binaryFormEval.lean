-- Prove2me | Theorems.Thm_HeckeEis_exists_retraction_binaryFormEval
-- name    : HeckeEis.exists_retraction_binaryFormEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/139ad2b7-6c8e-5bd4-b0ea-4984b53457ab
-- title:
--   Symᵖ⁻¹ as an equivariant summand of K[P¹(𝔽ₚ)]
-- statement:
--   Let $p$ be a prime and let $K$ be a field of characteristic $p$. Write $V =$ [`HeckeEis.BinaryForm K (p - 1)`](def/HeckeEis_BinaryFormRep.html#L25) for the $K$-submodule of $K[X_0,X_1]$ of polynomials homogeneous of degree $p-1$, and $W =$ [`ModularCurve.ProjectiveLine (ZMod p) → K`](def/ModularCurve_ProjectiveLine.html#L41) for the $K$-module of functions on $\mathbb{P}^1(\mathbb{Z}/p)$, the latter being the quotient of the set of unimodular rows over $\mathbb{Z}/p$ by scaling by units. Let $\mathrm{ev} =$ [`HeckeEis.binaryFormEval p K`](def/HeckeEis_BinaryFormRep.html#L114) $: V \to W$ be the map sending $F$ to the function whose value at the class of a unimodular row $(a,b)$ is the evaluation of $F$ at the images of $a,b$ under $\mathbb{Z}/p \to K$. The assertion is that there exists a $K$-linear map $r : W \to V$ such that: (i) $r \circ \mathrm{ev} = \mathrm{id}_V$; (ii) for every $g \in \mathrm{SL}_2(\mathbb{Z})$, $r \circ \rho_W(g) = \rho_V(g) \circ r$, where $\rho_W(g)$ is precomposition of functions with the action of $g$ on $\mathbb{P}^1(\mathbb{Z}/p)$ by right multiplication by the reduction of $g$ (the identity if that reduction has non-unit determinant) and $\rho_V(g)$ is the substitution $X_j \mapsto \sum_i g_{ij} X_i$ on binary forms; and (iii) for every natural number $\ell$ coprime to $p$, $r \circ A_W(\ell) = A_V(\ell) \circ r$, where $A_W(\ell)$ is precomposition with the action of $\begin{pmatrix} \ell & 0 \\ 0 & 1\end{pmatrix}$ on $\mathbb{P}^1(\mathbb{Z}/p)$ and $A_V(\ell)$ is the substitution by that same matrix on degree-$(p-1)$ forms. Thus $\mathrm{ev}$ is a split injection, with a retraction compatible both with the $\mathrm{SL}_2(\mathbb{Z})$-actions and with the two families of $\ell$-substitution operators.
--
--   This records that, in characteristic $p$, the space of binary forms of degree $p-1$ is a direct summand of the space of functions on $\mathbb{P}^1(\mathbb{F}_p)$, compatibly with $\mathrm{SL}_2(\mathbb{Z})$ and with the matrices $\mathrm{diag}(\ell,1)$ that enter the Hecke operators at $\ell \nmid p$ — the classical splitting $K[\mathbb{P}^1(\mathbb{F}_p)] = \mathbf{1} \oplus \mathrm{St}$ together with $\mathrm{St} \cong \mathrm{Sym}^{p-1}$. It is used by [`WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ`](thm.html#WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ), where Hecke-equivariant transfer between weight $p-1$ forms and functions on the projective line is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_retraction_binaryFormEval.lean

import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_retraction_binaryFormEval (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    ∃ r : (ModularCurve.ProjectiveLine (ZMod p) → K) →ₗ[K] HeckeEis.BinaryForm K (p - 1),
      r ∘ₗ HeckeEis.binaryFormEval p K = LinearMap.id ∧
      (∀ g : SL(2, ℤ), r ∘ₗ HeckeEis.projLineRepSL p K g = HeckeEis.binaryFormRepSL K (p - 1) g ∘ₗ r) ∧
      (∀ ℓ : ℕ, p.Coprime ℓ →
        r ∘ₗ HeckeEis.projLineAlphaAdj p K ℓ = HeckeEis.binaryFormAlphaAdj K (p - 1) ℓ ∘ₗ r) := by sorry
