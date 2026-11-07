-- Prove2me | Theorems.Thm_OnlineCAP_lemma_4_5
-- name    : OnlineCAP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:55.84973+00:00
-- url     : https://prove2.me/theorems/700cb8dc-e057-4f9d-8e52-f0838a4d568a
-- title:
--   Lemma 4.5 — z is monotone and feasible, A increases, |A(R)| ≥ n and a_p ≤ 4n x_p
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a finite point set with $n=|P|$, and let $x\ge0$ be a fractional vector on $P$; let $z$ be the vector of eq. (2), $a_p=\lceil nz_p\rceil$, $A$ the set of active copies and $A(R)=A\cap\pi^{-1}(R)$.
--
--   1. **Monotone.** If $x\le x'$ coordinatewise, then $z(x)\le z(x')$ and $A(x)\subseteq A(x')$.
--   2. **Feasible.** For every $R\subseteq P$ with $x(R)=\sum_{p\in R}x_p\ge1$:
--   $$z(R)\ge1\qquad\text{and}\qquad|A(R)|\ge n .$$
--   3. For every point $p\in P$:
--   $$|A\cap\pi^{-1}(p)|=a_p\le4n\,x_p .$$
--
--   Applied to the fractional solutions $x^1\le x^2\le\cdots$ of Algorithm 2 this says that $z^t$ is a monotone fractional hitting set, $A^1\subseteq A^2\subseteq\cdots$, every request has at least $n$ active copies, and a point has at most $4nx^t_p$ active copies.
--
--   Differences from the source:
--   - generalization: the monotone sequence x¹ ≤ x² ≤ ⋯ of fractional solutions and the requests R_t → one vector x ≥ 0 (and a pair x ≤ x′ for monotonicity), and every R ⊆ P with x(R) ≥ 1; reason: each clause concerns one time step or two consecutive ones, and none uses the bottomless shape; applied to x^t, to (x^{t−1}, x^t) and to R_t ∩ P it gives the source's statement
--   - generalization: n ≥ 1 points (standing assumption, p.15) → any finite P; reason: for P = ∅ every clause is trivial
--   - encoding: the first a_p copies {p} × [a_p] → the copies (p, i) with i < a_p, copies numbered 0, …, n − 1; reason: same sets
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Lemma 4.5, p.16 (proof pp.16–17)

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_zvec
import Definitions.Def_OnlineCAP_acount
import Definitions.Def_OnlineCAP_active
import Definitions.Def_OnlineCAP_activeOn

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Lemma 4.5 (activated copies).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Lemma 4.5, p.16 (PDF p.16): "The vector zt is monotone
and feasible, the sets At are increasing (A1 ⊆ A2 ⊆ · · · ), and for any request Rt and every point
p ∈ P, |At(Rt)| ≥ n, |At ∩ π−1(p)| = at_p ≤ 4n xt_p."

Let `P` be a finite point set with `n = |P|` and let `x ≥ 0` be a vector on `P`; `z`, `a`, `A` are
built from `x` by eq. (2) and §4.1.2.
1. (Monotone.) If `x ≤ x'` coordinatewise, then `z(x) ≤ z(x')` and `A(x) ⊆ A(x')`.
2. (Feasible.) For every `R ⊆ P` with `x(R) ≥ 1`: `z(R) ≥ 1` and `|A(R)| ≥ n`.
3. For every point `p`: `|A ∩ π⁻¹(p)| = a_p ≤ 4n x_p`.

**Formalization Note.** Stated for one vector (or a pair `x ≤ x'`) instead of a monotone sequence
`x¹ ≤ x² ≤ ⋯` of fractional hitting sets; applied to `x^t` and to the pairs `x^{t−1} ≤ x^t` it gives
the sequence statement. "Feasible" for the request `R_t` is `x^t(R_t) ≥ 1`, and `R` ranges over all
subsets of `P`, not only bottomless rectangles. -/
theorem lemma_4_5 (P : Finset (ℝ × ℝ)) (x x' : ↥P → ℝ) (hx : ∀ p, 0 ≤ x p) :
    ((∀ p, x p ≤ x' p) → (∀ p, zvec P x p ≤ zvec P x' p) ∧ active P x ⊆ active P x') ∧
    (∀ R : Set ↥P, 1 ≤ ∑ p, R.indicator x p →
      1 ≤ ∑ p, R.indicator (zvec P x) p ∧ P.card ≤ (activeOn P x R).card) ∧
    (∀ p : ↥P, ((active P x).filter (fun e => e.1 = p)).card = acount P x p ∧
      (acount P x p : ℝ) ≤ 4 * P.card * x p) := by sorry

end OnlineCAP
