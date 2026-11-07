-- Prove2me | Theorems.Thm_MixScale_theorem_H_3
-- name    : MixScale.theorem_H_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:12:57.964347+00:00
-- url     : https://prove2.me/theorems/f53ca89b-a19b-4932-bc02-96308dddb5fc
-- title:
--   Theorem H.3, p.51 — sharp equal-weight law, bound (100)
-- statement:
--   Let the profile satisfy Definition F.1 with witnessing integer $m>q+\alpha-\min(q,1)/2$, and $\tau=\min(q,1)$. There are fixed condition bounds and a univariate subclass with $k_0=2^m$ components, all weights $1/k_0$, such that every estimator succeeding with probability at least $2/3$ requires
--
--   $$N\ge c\,\ell_q(\gamma)\gamma^{-(2q-\tau)}\varepsilon^{-2},\qquad0<\gamma\le c^*,\ 0<\varepsilon\le\gamma/8,$$
--
--   even when both the center multiset and the scale multiset are supplied; the two multisets agree under the testing alternatives, though the scale multiset may depend on $\varepsilon$.
--
--   This shows that the upper bound of Theorem H.2 is sharp in $\gamma,\varepsilon$.
--
--   Differences from the source:
--   - encoding: Definition F.1 (L¹ derivative, ∂_s^j ĥ_v, continuous representatives, a.e. meaning at infinite-density points) → ∃ m, M_der; L¹ difference-quotient limit written with lower integrals; derivatives within {|s| ≥ 1}, assumed C^{M_der} there; h_v^{(m)} of an ∃-quantified representative C^m off zero; density f real valued; reason: these are the printed conditions; f(0) does not matter and no extra smoothness is added
--   - encoding: every estimator (possibly randomized) → any function of the samples and an independent seed on any probability space, with success via ∃ measurable E ⊆ {success}; reason: a measurable estimator has its ordinary success probability; no measurability is assumed
--   - encoding: c∗ positive → c∗ ≤ 1 in addition; reason: the model has γ ≤ 1 (p.2), so c∗ can be replaced by min(c∗, 1)
--   - generalization: a fixed-size one-dimensional subclass on which every estimator succeeding with probability at least 2/3 requires N ≥ …, even with supplied centers (and scale multiset for eq) → for each γ, ε a two-point pair in the subclass with equal center lists (and equal scale multisets for eq), and any randomized estimator succeeding on both; reason: an estimator succeeding on any subclass containing the pair succeeds on both; supplied data are constant on the pair, so the estimator depending on them is one estimator
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Theorem H.3, p.51 (PDF p.53), (100)

import Mathlib
import Definitions.Def_MixScale_Regular
import Definitions.Def_MixScale_Laws

namespace MixScale

/-- **Theorem H.3** (Sharp equal-weight law).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Theorem H.3, p.51 (PDF p.53), bound (100).

**Formalization Note.** The lower law for `W = eq` with `k₀ = 2^m` components. `HardPair` requires
all weights `1/k₀`, identical center lists and equal scale multisets (the pair may depend on `ε`).
The final sentence about Laplace points to Theorem H.7, not formalized here. -/
theorem theorem_H_3 (S : ProfileSpec) (m Mder : ℕ) (hS : IsRegularProfileAt S m Mder) :
    LowerLaw S .eq (2 ^ m) := by sorry

end MixScale
