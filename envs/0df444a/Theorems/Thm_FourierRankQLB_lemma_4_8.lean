-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_4_8
-- name    : FourierRankQLB.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:46.651085+00:00
-- url     : https://prove2.me/theorems/2162fce9-6157-4018-bad9-dc6c7cb58745
-- title:
--   Lemma 4.8 — determinant prediction from a scalar estimate
-- statement:
--   Let $d\ge2$ be even. Suppose that a procedure returns a real number $\widetilde Z$ such that, for every $Q\in O(d)$ and every sign vector $v$,
--   $$
--   P\Bigl[\bigl|\widetilde Z-Z(Q,v)\bigr|\le\frac1{200}\Bigr]\ge\frac23 .
--   $$
--   Then the predictor of §4.4 (sample $v$, run the procedure $125$ times independently, take the median, output $-1$ exactly when the median exceeds $9/16$) succeeds with probability greater than
--   $$
--   \frac12+\frac1{2000},
--   $$
--   averaged over $Q\sim\mu_d$, the vector $v$ and the internal randomness of the procedure.
--
--   It is the bridge from scalar estimation to determinant prediction, at the cost of $125$ invocations.
--
--   Differences from the source:
--
--   - encoding: a procedure with internal randomness → a Markov kernel from $O(d)$ to $\mathbb R$ for each sign vector; reason: the kernel is the law of the output, and measurability in $Q$ is what makes the average over $Q$ meaningful
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 4.8, p.30

import Mathlib
import Definitions.Def_FourierRankQLB_predictorSuccess
import Definitions.Def_FourierRankQLB_Zstat
import Definitions.Def_FourierRankQLB_signObj

open MeasureTheory ProbabilityTheory

namespace FourierRankQLB

/-- Lemma 4.8 (Determinant prediction from a scalar estimate). If, for every `Q ∈ O(d)` and every sign
vector `v`, the procedure satisfies `P[|Z̃ - Z(Q, v)| ≤ 1/200] ≥ 2/3`, then the predictor of §4.4
succeeds with probability greater than `1/2 + 1/2000`, averaged over `Q ∼ μ_d`, the vector `v` and the
internal randomness of the procedure.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 4.8, p. 30, with the predictor of p. 29.

**Formalization Note.** The procedure is a Markov kernel from `O(d)` to `ℝ` for each sign vector,
which makes the average over `Q` meaningful. `d` is even and at least `2`, the standing assumption of
§4.3. -/
theorem lemma_4_8 {d : ℕ} (hd : 2 ≤ d) (hev : Even d) (κ : SignVec d → Kernel (Od d) ℝ)
    [∀ σ, IsMarkovKernel (κ σ)]
    (hκ : ∀ (Q : Od d) (σ : SignVec d),
      2 / 3 ≤ (κ σ Q).real {z | |z - Zstat Q (signObj σ)| ≤ 1 / 200}) :
    1 / 2 + 1 / 2000 < predictorSuccess κ := by sorry

end FourierRankQLB
