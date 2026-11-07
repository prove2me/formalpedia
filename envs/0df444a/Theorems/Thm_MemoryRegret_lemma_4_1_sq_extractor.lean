-- Prove2me | Theorems.Thm_MemoryRegret_lemma_4_1_sq_extractor
-- name    : MemoryRegret.lemma_4_1_sq_extractor
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:01.864919+00:00
-- url     : https://prove2.me/theorems/3cfad0ad-5a6f-4b68-9b29-557b5b7cceb9
-- title:
--   Lemma 4.1 — near-orthogonal functions give an $L_2$-extractor
-- statement:
--   Let $\mu$ be a probability distribution on a finite set $X$ and let $f_1,\dots,f_d:X\to\{0,1\}$, $d\ge1$, satisfy
--   $$\Bigl|\mathbb E_{x\sim\mu}\bigl[(-1)^{f_i(x)+f_j(x)}\bigr]\Bigr|\le\frac1d\qquad\text{for all } i\ne j.$$
--   Then the matrix $M(x,i)=(-1)^{f_i(x)}$ on $X\times[d]$ is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$, for
--   $$k=\tfrac18\log_2 d-1,\qquad \ell=\tfrac14\log_2 d,\qquad r=\tfrac18\log_2 d.$$
--
--   This turns the statistical query dimension into the extractor property needed by the memory lower bound.
--
--   **Formalization Note** The extractor property is monotone in $(k,\ell,r)$, so these explicit values give the printed "$k=\ell=r=\Omega(\log d)$ for large enough $d$" (for instance with constant $1/16$ when $d\ge2^{16}$).
--
--   Differences from the source:
--   - generalization: SQDim_µ(H) = d, with its d near-orthogonal witnesses f_i ∈ H → any family f : Fin d → X → Bool with the near-orthogonality condition; reason: the source uses SQDim_µ(H) = d only through the witnesses; the witnesses of Definition 2 are such a family
--   - generalization: for large enough d, k = ℓ = r = Ω(log d) → for every d ≥ 1, k = ⅛log₂d − 1, ℓ = ¼log₂d, r = ⅛log₂d; reason: these are the values of the proof (p.30, last line); the printed form follows by monotonicity of the extractor property
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 4.1, p.29, with the constants of its proof, p.30

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_sqDim
import Definitions.Def_MemoryRegret_IsL2Extractor

namespace MemoryRegret

/-- **Lemma 4.1 (SQ dimension implies an L2-extractor).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 4.1, p.29, with the constants of its proof (p.30, last line).

Let `µ` be a probability distribution on a finite set `X` and `f_1, …, f_d : X → {0,1}`,
`d ≥ 1`, with `|E_{x∼µ}[(−1)^{f_i(x)+f_j(x)}]| ≤ 1/d` for all `i ≠ j`. Then the matrix
`M(x, i) = (−1)^{f_i(x)}` on `X × [d]` is a `(k, ℓ)`-L2-extractor with error `2^{−r}` with respect
to `µ` for `k = ⅛ log₂ d − 1`, `ℓ = ¼ log₂ d`, `r = ⅛ log₂ d`.

**Formalization Note.** The lemma's hypothesis "SQDim_µ(H) = d" is used only through the `d`
near-orthogonal witnesses, which are the hypothesis here (any such family, not only one of
maximal size). The printed conclusion "for large enough d, … k = ℓ = r = Ω(log d)" follows
from the explicit parameters, which the proof derives for every `d ≥ 1`, because the extractor
property is monotone in `(k, ℓ, r)`. Logarithms are base 2. -/
theorem lemma_4_1_sq_extractor {X : Type} [Fintype X] (μ : X → ℝ) (hμ : IsProbVec μ)
    (d : ℕ) (hd : 1 ≤ d) (f : Fin d → X → Bool)
    (horth : ∀ i j, i ≠ j → |corrWrt μ (f i) (f j)| ≤ 1 / (d : ℝ)) :
    IsL2Extractor μ f (Real.logb 2 d / 8 - 1) (Real.logb 2 d / 4) (Real.logb 2 d / 8) := by sorry

end MemoryRegret
