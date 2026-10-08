-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_properties_2_6_to_2_9
-- name    : GoldfarbIdnani.DualQP.properties_2_6_to_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:14:47.245546+00:00
-- url     : https://prove2.me/theorems/51f08812-d9cc-4e1f-a766-eb639c52d74c
-- title:
--   Properties (2.6)–(2.9) of the reduced inverse Hessian $H$ and the pseudo-inverse $N^*$
-- statement:
--   Let $G$ be an $n \times n$ symmetric positive definite matrix and let $A$ be a set of constraint indices whose normals $n_i$, $i \in A$, are linearly independent. Let $N$ be the matrix with columns $n_i$, $i\in A$, and let
--
--   $$
--   N^* = (N^{\mathsf T}G^{-1}N)^{-1}N^{\mathsf T}G^{-1}, \qquad H = G^{-1} - G^{-1}N(N^{\mathsf T}G^{-1}N)^{-1}N^{\mathsf T}G^{-1}
--   $$
--
--   be the operators (2.1)–(2.2). Then
--
--   1. for every $w \in \mathbb R^n$, $Hw = 0$ if and only if $w = N\alpha$ for some $\alpha \in \mathbb R^{|A|}$; (2.6)
--   2. $H$ is symmetric positive semi-definite; (2.7)
--   3. $HGH = H$; (2.8)
--   4. $N^*GH = 0$. (2.9)
--
--   These identities are used throughout the proofs of Lemma 1 and Theorems 1–2: (2.6) decides whether the new normal $n^+$ lies in the span of the active normals, and (2.7)–(2.8) give $z^{\mathsf T}n^+ = z^{\mathsf T}Gz > 0$ for $z = Hn^+ \ne 0$.
--
--   **Formalization Note.** The paper also lists (2.10), printed as $HH^+ = H^+$; as printed it fails unless $G = I$ (take $A = \emptyset$, so $H = G^{-1}$), no argument in Sections 2–3 uses it, and it is not part of this statement. "Positive semi-definite" is Mathlib's `Matrix.PosSemidef`, which includes symmetry; $H$ is symmetric because $G$ is.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 5, Section 2, Properties (2.6)–(2.9)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_QP

namespace GoldfarbIdnani.DualQP

open Matrix

theorem properties_2_6_to_2_9 {n m : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (A : Finset (Fin m))
    (hG : G.PosDef) (hA : LinIndep C A) :
    (∀ w : Fin n → ℝ, Hmat G C A *ᵥ w = 0 ↔ ∃ α : A → ℝ, w = Nmat C A *ᵥ α) ∧
    (Hmat G C A).PosSemidef ∧
    Hmat G C A * G * Hmat G C A = Hmat G C A ∧
    Nstar G C A * G * Hmat G C A = 0 := by sorry

end GoldfarbIdnani.DualQP
