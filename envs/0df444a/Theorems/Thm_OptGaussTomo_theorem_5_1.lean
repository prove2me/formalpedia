-- Prove2me | Theorems.Thm_OptGaussTomo_theorem_5_1
-- name    : OptGaussTomo.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:01.381877+00:00
-- url     : https://prove2.me/theorems/c4b5b6d5-d7cf-4b03-84a2-7b1bb8531935
-- title:
--   Theorem 5.1 — bosonic Gaussian tomography upper bound, $O((m^2+\log\delta^{-1})/\varepsilon^2)$ copies
-- statement:
--   There is a universal constant $C>0$ such that for every $m\ge1$ and $0<\varepsilon,\delta<1$ some
--
--   $$
--   n\ \le\ C\,\frac{m^2+\log(\delta^{-1})}{\varepsilon^2}
--   $$
--
--   copies suffice: there is a measurement on $\sigma^{\otimes n}$ that, for every $m$-mode bosonic Gaussian state $\sigma$ (any mean, any covariance, pure or mixed, no energy bound), outputs an estimate $\hat\sigma$ with $P(\sigma,\hat\sigma)\le\varepsilon$ with probability at least $1-\delta$.
--
--   Differences from the source:
--   - reading: O((m² + log(δ⁻¹))/ε²) copies → one universal constant C > 0, fixed before m, ε, δ, and some n ≤ C(m² + log δ⁻¹)/ε²; reason: meaning of O(·) uniform in m, ε, δ; log is natural; the range 0 < ε, δ < 1 is the one printed in Corollary C.6 and Theorem D.15
--   - encoding: a tomography protocol using n copies → an n-copy POVM with density-operator outcomes, fixed before the unknown state (Learns); reason: any measurement with classical post-processing is such a POVM; the protocol may not depend on the state
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem 5.1 p.14 (pdf p.14)

import Mathlib
import Definitions.Def_OptGaussTomo_Learns
import Definitions.Def_OptGaussTomo_purifiedDist
import Definitions.Def_OptGaussTomo_boseGauss

namespace OptGaussTomo

/-- **Theorem 5.1** (Bosonic Gaussian tomography, upper bound; Chen, Fanizza, Girardi, Lami, Mele,
Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847,
held version, sha256 0f7548a2…, Theorem 5.1, p.14). There exists a tomography protocol for `m`-mode
bosonic Gaussian states `σ` that outputs an estimate `σ̂` with purified distance at most
`P(σ, σ̂) ≤ ε` with probability at least `1 − δ`, using `O((m² + log(δ⁻¹))/ε²)` copies of `σ`.

**Formalization Note.** `O(·)` is one universal constant `C > 0`, fixed before `m ≥ 1` and
`0 < ε, δ < 1` (the range printed in Theorem D.15). The class `boseGauss m` is every bosonic
Gaussian state, with any mean and covariance and **no energy bound** (abstract: "independently of
any energy bound"). A protocol is an `n`-copy POVM with state-valued outcomes fixed before the
unknown state (`Learns`). `log` is natural. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
        Learns (boseGauss m) purifiedDist n ε δ := by sorry

end OptGaussTomo
