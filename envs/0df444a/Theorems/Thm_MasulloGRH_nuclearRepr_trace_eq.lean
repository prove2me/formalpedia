-- Prove2me | Theorems.Thm_MasulloGRH_nuclearRepr_trace_eq
-- name    : MasulloGRH.nuclearRepr_trace_eq
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:47.625514+00:00
-- url     : https://prove2.me/theorems/7da8dd07-3ec5-4251-a0fc-10a37ec66bb5
-- title:
--   Proposition C.3.2.1 — the nuclear trace $\sum_m\lambda_m\langle x_m,\varphi_m\rangle$ is independent of the representation, on spaces with the approximation property
-- statement:
--   **Well-posedness of the nuclear trace (Grothendieck; Litvinov).**
--
--   All vector spaces are over $\mathbb C$. A **Banach disc** of a topological vector space $F$ is a non-empty bounded convex circled subset $B\subseteq F$ whose linear span $F_B=\bigcup_{m\ge1}mB$, normed by the Minkowski functional $p_B$ of $B$, is a Banach space. A continuous linear map $T:E\to F$ is **nuclear** if it has a **nuclear representation**
--   $$T=\sum_{n}\lambda_n\,\langle\cdot,\varphi_n\rangle\,y_n ,$$
--   that is, $Tx=\sum_n\lambda_n\varphi_n(x)\,y_n$ for all $x\in E$, where $\sum_n|\lambda_n|<\infty$, $(\varphi_n)$ is an equicontinuous sequence in the dual $E'$ and $(y_n)$ is a sequence contained in a Banach disc of $F$.
--
--   A topological vector space $E$ has the **approximation property** if the identity of $E$ is a limit of continuous linear maps of finite rank, uniformly on every pre-compact subset of $E$.
--
--   Let $E$ be a Hausdorff locally convex space with the approximation property and let $A:E\to E$ be a nuclear operator. For every nuclear representation
--   $$A=\sum_{m}\lambda_m\,\langle\cdot,\varphi_m\rangle_{E,E'}\,x_m$$
--   the series $\sum_m\lambda_m\langle x_m,\varphi_m\rangle_{E,E'}$ converges absolutely, and its sum
--   $$\operatorname{Trace}(A):=\sum_{m}\lambda_m\,\langle x_m,\varphi_m\rangle_{E,E'}$$
--   does not depend on the choice of $(\lambda_m)$, $(\varphi_m)$, $(x_m)$, but only on $A$: any two nuclear representations of $A$ give the same value.
--
--   This number is the **nuclear trace** of $A$. Without the approximation property the trace of a nuclear operator need not be well defined, which is why the hypothesis appears; it holds for Hilbert spaces and for nuclear spaces. The paper computes its trace formula with this notion of trace.
--
--   **Formalization Note.** `IsHLCS` (from `Def_MasulloGRH_LocallyConvex`) means that the topology is defined by a family of seminorms and is Hausdorff. `IsNuclearMap`, `IsNuclearRepr` and `IsBanachDisc` are the definitions of `Def_MasulloGRH_NuclearMap`: a nuclear representation consists of sequences indexed by $\mathbb N$, the series converges unconditionally in $F$ (`HasSum`), and the Minkowski functional $p_B$ is Mathlib's `gauge B`. `HasApproximationProperty ℂ E` is the definition of `Def_TopologicalTensorProduct_ApproximationProperty` (uniform approximation of the identity on pre-compact sets). The statement is the equality of the two sums `∑' m, c m * φ m (x m)` for two arbitrary representations, together with absolute summability (so that `∑'` is a genuine sum and not a junk value).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 694, Proposition C.3.2.1, (C.3.2.1)–(C.3.2.2); classical reference: G. L. Litvinov, Approximation Properties of Locally Convex Spaces and the Problem of Uniqueness of the Trace of a Linear Operator, Selecta Mathematica Sovietica 11 (1992), no. 1, pp. 25-40, §4.2, Thm. 1

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Filter Topology TopologicalTensorProduct
set_option autoImplicit false

namespace MasulloGRH

theorem nuclearRepr_trace_eq {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (hAP : HasApproximationProperty ℂ E) (A : E →L[ℂ] E)
    (c c' : ℕ → ℂ) (φ φ' : ℕ → StrongDual ℂ E) (x x' : ℕ → E)
    (h : IsNuclearRepr A c φ x) (h' : IsNuclearRepr A c' φ' x') :
    Summable (fun m => ‖c m * φ m (x m)‖) ∧
      ∑' m, c m * φ m (x m) = ∑' m, c' m * φ' m (x' m) := by sorry

end MasulloGRH
