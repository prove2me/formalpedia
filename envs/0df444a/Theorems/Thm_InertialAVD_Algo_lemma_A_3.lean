-- Prove2me | Theorems.Thm_InertialAVD_Algo_lemma_A_3
-- name    : InertialAVD.Algo.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:52.304183+00:00
-- url     : https://prove2.me/theorems/7e8e3a81-7cf3-4946-bd94-9d187c5af1dc
-- title:
--   Lemma A.3 — Opial's lemma, discrete form
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $S\subseteq\mathcal H$ a nonempty set and $(x_k)_{k\ge0}$ a sequence in $\mathcal H$. Assume that
--
--   1. for every $z\in S$, $\lim_{k\to+\infty}\|x_k-z\|$ exists;
--   2. every weak sequential limit point of $(x_k)$ belongs to $S$, i.e. whenever $x_{k_n}\rightharpoonup p$ weakly along a strictly increasing sequence $k_n$, then $p\in S$.
--
--   Then there is $\bar x\in S$ with
--
--   $$x_k\rightharpoonup\bar x\quad\text{weakly as }k\to\infty .$$
--
--   Opial's lemma is the standard tool for proving weak convergence of iterates of optimization algorithms; here it is applied with $S=\operatorname{argmin}(\Phi+\Psi)$.
--
--   **Formalization Note.** Weak convergence is the published `WeakTendsto` ($\langle x_k,v\rangle\to\langle\bar x,v\rangle$ for every $v$). A weak sequential limit point is a $p$ with `WeakTendsto (x ∘ φ) p` for some strictly monotone $\varphi:\mathbb N\to\mathbb N$. Completeness of $\mathcal H$ is assumed.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 24, Lemma A.3

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open Filter Topology

namespace InertialAVD.Algo

/-- Lemma A.3, p. 24 (Opial's lemma, discrete). Let `S ⊆ H` be nonempty and `(x_k)` a sequence in
the Hilbert space `H` such that (i) for every `z ∈ S`, `lim ‖x_k − z‖` exists, and (ii) every weak
sequential limit point of `(x_k)` belongs to `S`. Then `x_k` converges weakly to a point of `S`. -/
theorem lemma_A_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set H) (x : ℕ → H) (hS : S.Nonempty)
    (hi : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun k => ‖x k - z‖) atTop (𝓝 l))
    (hii : ∀ p : H, (∃ φ : ℕ → ℕ, StrictMono φ ∧ InertialFB.IFB.WeakTendsto (x ∘ φ) p) → p ∈ S) :
    ∃ xbar ∈ S, InertialFB.IFB.WeakTendsto x xbar := by sorry

end InertialAVD.Algo
