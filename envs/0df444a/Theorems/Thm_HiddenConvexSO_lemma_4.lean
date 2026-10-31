-- Prove2me | Theorems.Thm_HiddenConvexSO_lemma_4
-- name    : HiddenConvexSO.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:49.634196+00:00
-- url     : https://prove2.me/theorems/3906cae8-63a4-40ec-8ec8-dd32ac74421e
-- title:
--   Lemma 4 — a loop through two points of $H\cap\mathrm{SO}(n)$ that stays on one side of $H$ on each half
-- statement:
--   Let $A\in\mathbb R^{n\times n}$, $c\in\mathbb R$, and $H=\{X\in\mathbb R^{n\times n}:\langle A,X\rangle=c\}$, where $\langle A,X\rangle=\operatorname{tr}(A^\top X)$. Let $U,V\in H\cap\mathrm{SO}(n)$. Then there is a continuous $\gamma:[0,1]\to\mathrm{SO}(n)$ such that
--
--   1. $\gamma(0)=\gamma(1)=U$;
--   2. $\gamma(1/2)=V$;
--   3. either $\langle A,\gamma(t)\rangle=c$ for all $t\in(0,\tfrac12)$, or $\langle A,\gamma(t)\rangle>c$ for all $t\in(0,\tfrac12)$;
--   4. either $\langle A,\gamma(t)\rangle=c$ for all $t\in(\tfrac12,1)$, or $\langle A,\gamma(t)\rangle<c$ for all $t\in(\tfrac12,1)$.
--
--   The loop goes from $U$ to $V$ on or above the hyperplane $H$ and returns below it (or within it). In the proof of Theorem 3 it is the loop whose image under $X\mapsto(\langle A,X\rangle-c,\ \mathrm{dist}_{\mathcal U}(X)-\delta/2)$ winds around the origin.
--
--   **Formalization Note** $\langle A,X\rangle$ is `traceInner A X` $=\sum_{i,j}A_{ij}X_{ij}$; $\gamma$ is a Mathlib `Path U U` in the subtype `Matrix.specialOrthogonalGroup (Fin n) ℝ`; $\gamma(1/2)=V$ is stated for the point $t\in[0,1]$ with $t=1/2$. Each "either … or" is a disjunction of two statements, each quantified over the whole open interval. No condition on $n$, $A$, $c$, and $U=V$ is allowed.
--
--   Differences from the source:
--   - encoding: SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1} with the subspace topology (p.1, p.13) → Matrix.specialOrthogonalGroup (Fin n) ℝ (star A * A = 1 ∧ A * star A = 1 ∧ det A = 1), coerced subtype topology; 0-based indices; reason: Lean convention; for real square matrices AᵀA = I already gives AAᵀ = I, so the same set
--   - encoding: ⟨A, X⟩ = tr(AᵀX) (p.2) → traceInner A X = Σᵢ Σⱼ A i j * X i j; reason: tr(AᵀX) = Σᵢⱼ Aᵢⱼ Xᵢⱼ; same value for every A, X
--   - encoding: continuous γ : [0,1] → SO(n) with γ(0) = γ(1) = U and γ(1/2) = V → γ : Path U U with γ t = V for the t ∈ unitInterval with (t : ℝ) = 1/2; reason: a Path is a continuous map on [0,1] with the given endpoints; same objects
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, Lemma 4, p.14 (H defined on p.14)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner

namespace HiddenConvexSO

open WainwrightHDS.NucNorm

/-- **Lemma 4: a loop through two points of a level set that stays on one side on each half.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, Lemma 4, p.14 (PDF p.14), with
`H = {X ∈ ℝ^{n×n} : ⟨A, X⟩ = c}` (p.14): "Let U, V ∈ H ∩ SO(n). Then, there exists a continuous
function γ : [0, 1] → SO(n) with the following properties: • γ(0) = γ(1) = U, • γ(1/2) = V,
• either ⟨A, γ(t)⟩ = c for all t ∈ (0, 1/2) or ⟨A, γ(t)⟩ > c for all t ∈ (0, 1/2), and • either
⟨A, γ(t)⟩ = c for all t ∈ (1/2, 1) or ⟨A, γ(t)⟩ < c for all t ∈ (1/2, 1)."

**Formalization Note.** `⟨A, X⟩ = tr(AᵀX)` (p.2) is `traceInner A X = Σᵢ Σⱼ A i j * X i j`.
SO(n) is the subtype of `Matrix.specialOrthogonalGroup (Fin n) ℝ`; `γ` is a Mathlib `Path U U`
(continuous on `[0,1]`, `γ 0 = γ 1 = U`), and `γ(1/2) = V` is stated for the point `t` of `[0,1]`
with `t = 1/2`. Each "either … or" is a disjunction of two universally quantified statements over the
open interval. No restriction on `n`, `A`, `c`. -/
theorem lemma_4 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (U V : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hU : traceInner A (U : Matrix (Fin n) (Fin n) ℝ) = c)
    (hV : traceInner A (V : Matrix (Fin n) (Fin n) ℝ) = c) :
    ∃ γ : Path U U,
      (∀ t : unitInterval, (t : ℝ) = 1 / 2 → γ t = V) ∧
      ((∀ t : unitInterval, (t : ℝ) ∈ Set.Ioo 0 (1 / 2) →
          traceInner A (γ t : Matrix (Fin n) (Fin n) ℝ) = c) ∨
        (∀ t : unitInterval, (t : ℝ) ∈ Set.Ioo 0 (1 / 2) →
          c < traceInner A (γ t : Matrix (Fin n) (Fin n) ℝ))) ∧
      ((∀ t : unitInterval, (t : ℝ) ∈ Set.Ioo (1 / 2) 1 →
          traceInner A (γ t : Matrix (Fin n) (Fin n) ℝ) = c) ∨
        (∀ t : unitInterval, (t : ℝ) ∈ Set.Ioo (1 / 2) 1 →
          traceInner A (γ t : Matrix (Fin n) (Fin n) ℝ) < c)) := by sorry

end HiddenConvexSO
