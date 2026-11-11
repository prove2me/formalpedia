-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_claim_4_2
-- name    : InterleavedUnitaryNOF.LowerBound.claim_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:58.545194+00:00
-- url     : https://prove2.me/theorems/d92e1a75-e226-46f6-b6b8-f26a30cce0ce
-- title:
--   Claim 4.2 — continuous and rounded promise probabilities
-- statement:
--   Fix any eventually fitting power-of-two dimension schedule $m(n)=\Theta(\sqrt{n/\log_2n})$, and let $R$ round each real and imaginary coordinate to $2^{-b}\lceil2^bt-1/2\rceil$, where $b=\lceil\log_2n\rceil$, then encode and zero-pad the three groups separately. Write $\widetilde\mu_j=R_*\mu_j$ and $W=A_1B_1C_1D_1E_1A_2B_2C_2D_2E_2$. For all sufficiently large $n$,
--
--   $$ \Pr_{\mu_1}[\operatorname{Re}\operatorname{Tr}(W)/m\ge0.9]=1,\qquad \Pr_{\mu_0}[\operatorname{Re}\operatorname{Tr}(W)/m\le0.1]\ge1-1/m. $$
--
--   Every rounded matrix satisfies $\|U^\dagger U-I_m\|_F\le10^{-4}$, and
--
--   $$ \Pr_{\widetilde\mu_1}[F_n=1]=1,\qquad \Pr_{\widetilde\mu_0}[F_n=0]\ge1-1/m. $$
--
--   Here $F_n$ is the full near-unitary complex-matrix promise function. All continuous and rounded conclusions are retained.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: an unspecified fitting power-of-two Θ dimension choice → every eventually fitting Θ schedule, with positivity provided in the conclusion; reason: capacity and Θ assumptions are required only eventually, so no small-length vacuity is introduced
--   - encoding: rounding followed by inverse decoding and zero padding → ceil-based integer rounding, modular two’s-complement bits and separate zero-padded maps; reason: this is exactly the coordinate decoder and tie convention on pp.7,10
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Claim 4.2, printed p.10 = PDF p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem claim_4_2 (m : ℕ → ℕ) (hm : AdmissibleSchedule m) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∃ hmpos : NeZero (m n),
      letI := hmpos
      (mu1 (m n)) {u | (9 : ℝ)/10 ≤ normalizedTrace (matrices u)} = 1 ∧
      1 - 1/(m n : ℝ) ≤ ((mu0 (m n)) {u | normalizedTrace (matrices u) ≤ (1 : ℝ)/10}).toReal ∧
      (∀ u : ContinuousInput (m n),
        let v := roundInputs n u
        promisedMatrices (decode (m n) v.1 v.2.1 v.2.2)) ∧
      (roundedMu true n (m n)) {v | iup (m n) v.1 v.2.1 v.2.2 = some true} = 1 ∧
      1 - 1/(m n : ℝ) ≤ ((roundedMu false n (m n))
        {v | iup (m n) v.1 v.2.1 v.2.2 = some false}).toReal := by sorry

end InterleavedUnitaryNOF.LowerBound
