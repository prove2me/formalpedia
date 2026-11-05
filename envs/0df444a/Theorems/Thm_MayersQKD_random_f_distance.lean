-- Prove2me | Theorems.Thm_MayersQKD_random_f_distance
-- name    : MayersQKD.random_f_distance
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:37.265888+00:00
-- url     : https://prove2.me/theorems/393e7483-6af6-4d86-a503-87dd8e3c87cd
-- title:
--   §8, p.10 — a random $f$ has large minimum distance
-- statement:
--   Let $f$ be a uniformly random $(r+m)\times N$ boolean matrix and let $0<d\le 1/2$. Then the probability that some nonzero $y\in\mathrm{GF}(2)^{r+m}$ has $\mathrm{wt}(y^{\mathsf T}f)\le dN$ is at most
--
--   $$
--   2^{\,r+m+(H(d)-1)N},
--   $$
--
--   where $H(x)=-(x\lg x+(1-x)\lg(1-x))$.
--
--   For a fixed ratio $(r+m)/N$ and $d<H^{-1}(1-(r+m)/N)$ the exponent is negative and linear in $N$. This is the paper's statement that the code $C_0^\perp$ spanned by the rows of $f$ has minimum distance above $(H^{-1}(1-(r+m)/N)-\eta)N$ except with negligible probability.
--
--   Differences from the source:
--   - reading: "except with negligible probability" → the explicit bound 2^(r+m+(H(d)−1)N) on the fraction of bad matrices; reason: the bound is what "negligible" stands for and implies it for fixed η
--   - generalization: minimum distance of C₀⊥ at most dN → some nonzero y with wt(yᵀf) ≤ dN; reason: every nonzero codeword is yᵀf with y ≠ 0, so the printed bad event is contained in this one, which also contains the rank-deficient f (correction C1)
--   - encoding: d defined as the actual minimum distance over N, with η > 0 → a free d with 0 < d ≤ 1/2; reason: take d = H⁻¹(1 − (r+m)/N) − η
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §8, p.10

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_MayersQKD_Bits

namespace MayersQKD

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §8, p.10: because `f` is chosen at random, except with
negligible probability the code `C₀⊥` spanned by the rows of `f` has large minimum distance. Here
the explicit count: for `0 < d ≤ 1/2`, the fraction of the `(r+m) × N` matrices with a nonzero `y`
such that `wt(yᵀ f) ≤ dN` is at most `2^(r + m + (H(d) − 1) N)`.

**Formalization Note.** "Negligible" is replaced by the bound it stands for. With
`d < H⁻¹(1 − (r+m)/N)` the exponent is negative and linear in `N`. The quantity `wt(yᵀ f)` over all
nonzero `y` is the one Lemma 1 needs (correction C1); it also excludes rank-deficient `f`. -/
theorem random_f_distance (N r m : ℕ) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1 / 2) :
    ((Finset.univ.filter fun f : HashMatrix r m N =>
        ∃ y : Fin r ⊕ Fin m → ZMod 2, y ≠ 0 ∧ (hammingNorm (Matrix.vecMul y f) : ℝ) ≤ d * N).card : ℝ) /
      (2 : ℝ) ^ ((r + m) * N) ≤
    (2 : ℝ) ^ ((r : ℝ) + m + (WildeQIT.binaryEntropy d - 1) * N) := by sorry

end MayersQKD
