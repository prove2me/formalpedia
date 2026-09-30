-- Prove2me | Theorems.Thm_HeldKarp_Ascent_fejer_monotone_converges
-- name    : HeldKarp.Ascent.fejer_monotone_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:39:35.855749+00:00
-- url     : https://prove2.me/theorems/23c8e861-5b39-48e0-8636-dbef74f63f7a
-- title:
--   Féjer-monotone sequences relative to a full-dimensional set converge (Motzkin–Schoenberg)
-- statement:
--   Let $A \subseteq \mathbb R^d$ and let $(y^m)_{m \ge 0}$ be a sequence in $\mathbb R^d$. The sequence is **Féjer-monotone relative to $A$** if, for every $x \in A$, the Euclidean distances $\|y^m - x\|$ form a nonincreasing sequence in $m$. If $A$ has full dimension, i.e. contains a neighbourhood of some point (nonempty interior), then every sequence that is Féjer-monotone relative to $A$ converges:
--   $$\operatorname{int} A \neq \emptyset \ \text{ and } \ \|y^{m+1} - x\| \le \|y^m - x\| \ \ (\forall x \in A,\ \forall m) \quad\Longrightarrow\quad \lim_{m\to\infty} y^m \text{ exists}.$$
--
--   Held and Karp quote this result of Motzkin and Schoenberg (their reference [12]) in the proof of Lemma 3 and do not prove it; it is what turns the distance-decrease of Lemma 2 into convergence of the relaxation iteration.
--
--   **Formalization Note** Points are real vectors indexed by `Fin d`; monotonicity is stated for squared Euclidean distances (sums of squares), which is equivalent. Convergence is in the product topology, which on $\mathbb R^d$ is the Euclidean topology.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §2, proof of Lemma 3, p. 12 (PDF p. 7), unnumbered, quoting T. Motzkin and I. J. Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954) [12]

import Mathlib

open Filter Topology

namespace HeldKarp.Ascent

/-- **Convergence of Féjer-monotone sequences** (Motzkin–Schoenberg, quoted in the proof of
Lemma 3 of Held & Karp, *The traveling-salesman problem and minimum spanning trees: Part II*,
Math. Programming 1 (1971), §2, p. 12 (PDF p. 7), from their reference [12]; unnumbered):
"Let A be a point set and {y^m} a sequence of points. Then {y^m} is Féjer-monotone relative to A
if, for every x ∈ A, the sequence {‖y^m − x‖} is monotone nonincreasing. It is shown in [12] that,
if A is of full dimension (i.e., contains a neighborhood) then any sequence which is
Féjer-monotone relative to A converges."

Formalization Note: points are real `d`-vectors `Fin d → ℝ`; `‖·‖` is the Euclidean norm (as
everywhere in the paper), and monotonicity of `‖y^m − x‖` is stated for its square, a sum of
squares (equivalent). "Contains a neighborhood" is `(interior A).Nonempty`. Convergence is in the
product topology on `Fin d → ℝ`, which is the Euclidean topology. The paper cites this result and
does not prove it. -/
theorem fejer_monotone_converges {d : ℕ} (A : Set (Fin d → ℝ)) (hA : (interior A).Nonempty)
    (y : ℕ → Fin d → ℝ) (hy : ∀ x ∈ A, Antitone (fun m => ∑ i, (y m i - x i) ^ 2)) :
    ∃ p : Fin d → ℝ, Tendsto y atTop (𝓝 p) := by sorry

end HeldKarp.Ascent
