-- Prove2me | Theorems.Thm_MonoSkew_Main_lemma_2_2
-- name    : MonoSkew.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:44.089128+00:00
-- url     : https://prove2.me/theorems/af5a4da3-5947-498b-bb2d-629cc739c5c9
-- title:
--   Lemma 2.2 — quasi-Fejér sequences whose sequential weak cluster points lie in $C$ converge weakly to a point of $C$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, let $C$ be a nonempty subset of $\mathcal H$, and let $(x_n)_{n\in\mathbb N}$ be a sequence in $\mathcal H$. Suppose that, for every $x\in C$, there exists a summable sequence $(\varepsilon_n)_{n\in\mathbb N}$ in $[0,+\infty[$ such that
--   $$(\forall n\in\mathbb N)\qquad \|x_{n+1}-x\|^2\le\|x_n-x\|^2+\varepsilon_n,$$
--   and that every sequential weak cluster point of $(x_n)_{n\in\mathbb N}$ lies in $C$. Then $(x_n)_{n\in\mathbb N}$ converges weakly to a point of $C$.
--
--   This is the quasi-Fejér version of Opial's lemma. It is the device that turns the energy estimates of the forward–backward–forward method into weak convergence of its iterates.
--
--   **Formalization Note** The sequence $(\varepsilon_n)$ may depend on $x\in C$. A sequential weak cluster point is the weak limit of a subsequence $(x_{\varphi(k)})$ with $\varphi$ strictly increasing; weak convergence $u_k\rightharpoonup u$ means $\langle u_k,y\rangle\to\langle u,y\rangle$ for every $y$. Completeness of $\mathcal H$ is an explicit hypothesis (the paper's "Hilbert space").
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, p. 4, Lemma 2.2, (2.1)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Lemma 2.2 (p. 4): let `C` be a nonempty subset of a real Hilbert space `E` and `(x_n)` a
sequence in `E`. If for every `c ∈ C` there is a summable sequence `ε_n ≥ 0` with
`‖x_{n+1} − c‖² ≤ ‖x_n − c‖² + ε_n` for all `n`, and every sequential weak cluster point of
`(x_n)` lies in `C`, then `(x_n)` converges weakly to a point of `C`. -/
theorem lemma_2_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (hC : C.Nonempty) (x : ℕ → E)
    (hfej : ∀ c ∈ C, ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Summable ε ∧
      ∀ n, ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 + ε n)
    (hclus : ∀ w, IsSeqWeakClusterPt x w → w ∈ C) :
    ∃ c ∈ C, WeakTendsto x c := by sorry

end MonoSkew.Main
