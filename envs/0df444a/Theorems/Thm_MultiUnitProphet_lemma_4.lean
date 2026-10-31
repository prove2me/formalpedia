-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_4
-- name    : MultiUnitProphet.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:00.606013+00:00
-- url     : https://prove2.me/theorems/97f0bae9-5f59-47ca-918a-849d846ecefd
-- title:
--   Lemma 4 — (GenBern : $\min\mu$ s.t. $\delta=\phi$) has optimal value $\phi^\star_k(n)$
-- statement:
--   Let $0<k<n$. Over sums $X$ of $n$ independent Bernoullis with biases in $[0,1]$ and $\delta_k(X)=\phi^\star_k(n)$, the minimum of $\mu_k(X)$ is attained and equals $\phi^\star_k(n)$: the optimal values of (GenBern : $\min\phi$ s.t. $\delta=\mu=\phi$) and (GenBern : $\min\mu$ s.t. $\delta=\phi$) are equal.
--
--   This lets §5.2–5.3 study the simpler program with a fixed constraint value.
--
--   Differences from the source:
--   - reading: X is the sum of Bernoulli r.v.s (no count given) → n Bernoullis, the same n as in (GenBern : min φ s.t. δ = µ = φ); reason: the program is a reformulation of the first one for the same instance size
--   - reading: the optimal values are equal → IsLeast (genBernMuValues k n (phiStar k n)) (phiStar k n); reason: the paper writes min: the optimum is attained and equals φ⋆_k(n)
--   - encoding: a supply k > 0 and n > k (Lemma 3) → 0 < k < n; reason: the setting of Lemma 3, in which the programs are posed
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 4, p.11

import Mathlib
import Definitions.Def_MultiUnitProphet_GenBern

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 4: (GenBern : min µ s.t. δ = φ) has the same optimal value `φ⋆_k`.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 4, p.11: "The optimal values of the optimization problems
(GenBern : min ϕ s.t. δ = µ = ϕ) and (GenBern : min µ s.t. δ = ϕ) are equal."

For `0 < k < n`: over sums `X` of `n` independent Bernoullis with biases in `[0, 1]` and
`δ_k(X) = φ⋆_k(n)`, the least value of `µ_k(X)` exists and equals `φ⋆_k(n)`.

**Formalization Note.** "X is the sum of Bernoulli r.v.s" (p.11) is read with the same number `n`
of Bernoullis as in (GenBern : min φ s.t. δ = µ = φ). "Optimal value" is an attained minimum
(`IsLeast`). -/
theorem lemma_4 (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    IsLeast (genBernMuValues k n (phiStar k n)) (phiStar k n) := by sorry

end MultiUnitProphet
