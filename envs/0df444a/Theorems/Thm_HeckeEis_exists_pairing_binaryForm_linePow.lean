-- Prove2me | Theorems.Thm_HeckeEis_exists_pairing_binaryForm_linePow
-- name    : HeckeEis.exists_pairing_binaryForm_linePow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b04cdc68-d94e-52b6-afd5-12eb7ccba730
-- title:
--   An SL₂(ℤ)-invariant pairing on binary forms of degree n
-- statement:
--   Let $n$ be a natural number and let $V_n$ denote [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25), the submodule of $\mathbb{C}[X_0,X_1]$ (polynomials in two variables indexed by `Fin 2`) consisting of the forms homogeneous of degree $n$. The group $SL_2(\mathbb{Z})$ acts on $V_n$ through [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61), which sends $g$ to the restriction to $V_n$ of the algebra endomorphism of $\mathbb{C}[X_0,X_1]$ substituting $\sum_{i} g_{ij} X_i$ for $X_j$; and for $\tau \in \mathbb{C}$, [`HeckeEis.linePow n τ`](def/HeckeEis_EichlerIntegral.html#L22) is the element $(\tau X_0 + X_1)^n$ of $V_n$. The assertion is that there exists a $\mathbb{C}$-bilinear form $B \colon V_n \times V_n \to \mathbb{C}$ (given as an iterated linear map) satisfying four conditions: $B(gP, gQ) = B(P,Q)$ for all $g \in SL_2(\mathbb{Z})$ and all $P, Q \in V_n$; $B(Q,P) = (-1)^n B(P,Q)$ for all $P,Q$; the left radical of $B$ vanishes, i.e. any $P$ with $B(P,Q)=0$ for every $Q$ is zero; and the normalisation $B\bigl((\tau X_0 + X_1)^n, (\sigma X_0 + X_1)^n\bigr) = (\tau - \sigma)^n$ for all $\tau, \sigma \in \mathbb{C}$. Only the existence of such a $B$ is asserted, not uniqueness, and non-degeneracy is stated for the first argument alone.
--
--   This is the classical determinant (transvectant) pairing on binary forms of degree $n$, i.e. the $SL_2$-invariant, $(-1)^n$-symmetric form on $\mathrm{Sym}^n$ of the standard two-dimensional representation, pinned down on $n$-th powers of linear forms by $B(u^n,v^n)=[u,v]^n$. It is used in [`HeckeEis.exists_induced_binaryFormRepSL_top`](thm.html#HeckeEis.exists_induced_binaryFormRepSL_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_pairing_binaryForm_linePow.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_pairing_binaryForm_linePow (n : ℕ) :
    ∃ B : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ,
      (∀ (g : SL(2, ℤ)) (P Q : ↥(HeckeEis.BinaryForm ℂ n)),
          B (HeckeEis.binaryFormRepSL ℂ n g P) (HeckeEis.binaryFormRepSL ℂ n g Q) = B P Q) ∧
      (∀ P Q : ↥(HeckeEis.BinaryForm ℂ n), B Q P = (-1) ^ n * B P Q) ∧
      (∀ P : ↥(HeckeEis.BinaryForm ℂ n), (∀ Q : ↥(HeckeEis.BinaryForm ℂ n), B P Q = 0) → P = 0) ∧
      (∀ τ σ : ℂ, B (HeckeEis.linePow n τ) (HeckeEis.linePow n σ) = (τ - σ) ^ n) := by sorry
