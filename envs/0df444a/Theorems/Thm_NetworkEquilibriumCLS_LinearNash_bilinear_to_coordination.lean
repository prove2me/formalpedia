-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_bilinear_to_coordination
-- name    : NetworkEquilibriumCLS.LinearNash.bilinear_to_coordination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:51.891673+00:00
-- url     : https://prove2.me/theorems/409a5c92-cfc8-41a7-932a-c8c79563fadb
-- title:
--   Lemma 2.5 — exact bilinear KKT via an N+1-player coordination game
-- statement:
--   Let p(z)=βᵀz+Σ_{i<j}w_{ij}z_iz_j be any square-free quadratic with signed rational coefficients in a positive number N of variables. There is a uniform polynomial-time construction of a binary-action common-payoff network coordination game G on exactly N+1 players, with rational edge payoffs in [0,1], such that every real Nash equilibrium x satisfies
--
--   $$(x_1,\ldots,x_N)\text{ is an exact box KKT point of }p.$$
--
--   The extra player is last in the formal index convention; inducing the source point means dropping that coordinate. The guarantee holds for every real equilibrium, and hence for every encoded rational equilibrium. Signed coefficients, linear terms, and both endpoint KKT signs are retained. This is the game construction used between the KKT reduction and Main Theorem 2.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
--   - encoding: the auxiliary player is named 0 and the original players 1 through N → the original players occupy the first N Fin indices and the auxiliary player is last; reason: a bijective player relabelling; the decoder is explicit coordinate projection and rational projection has linear encoding cost
--   - encoding: p(z)=βᵀz+Σ_{i<j}w_{ij}z_iz_j → a Quadratic record ½zᵀQz+cᵀz with symmetric Q, zero diagonal, Q_ij=Q_ji=w_ij and c=β; reason: with zero diagonal ½zᵀQz=Σ_{i<j}Q_ij z_iz_j, so the two representations denote the same polynomials
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.7 (PDF 8), Lemma 2.5.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem bilinear_to_coordination :
    ∃ f : List Bool → List Bool, PolyTime f ∧
    ∀ (N : ℕ), 0 < N → ∀ p : Quadratic N, IsBilinear p →
      ∃ G : Coordination (N + 1), CoordinationValid G ∧ encCoordination G = f (encQuadratic p) ∧
        ∀ x : Fin (N + 1) → ℝ, CoordinationNash G x →
          QuadraticKKT p (fun i => x i.castSucc) := by sorry

end NetworkEquilibriumCLS.LinearNash
