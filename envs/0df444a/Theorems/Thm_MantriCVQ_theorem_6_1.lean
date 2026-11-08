-- Prove2me | Theorems.Thm_MantriCVQ_theorem_6_1
-- name    : MantriCVQ.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:52.154434+00:00
-- url     : https://prove2.me/theorems/6f90c856-bb13-420f-b015-c5aef99e673d
-- title:
--   Theorem 6.1 — light blocks in the first satisfied term, Eq. (6.1)
-- statement:
--   Let $\Phi$ be a DNF of width at most $W$ on $K$ independent blocks of dimension $m$ with a code family of degree $d$, let $t\ge0$ and $z\in\mathbb F_2^K$. For every integer $1\le\ell\le W$,
--   $$\Pr_\rho\bigl[\Phi(\rho(z))=1\text{ and at least }\ell\text{ blocks are light for the first satisfied term}\bigr]\le\binom K\ell\Bigl(\frac{2W}\ell\Bigr)^\ell\binom m{\le dt}^\ell2^{-m\ell}.$$
--   If $\ell>K$ the event is empty. The bound does not depend on the number of terms of $\Phi$, which is what lets the argument handle correlated projections. Each block's secret determines both its code table and its free leaf.
--
--   Differences from the source:
--   - generalization: a code family of Definition 3.1 → any family with the degree condition (CodeDeg d); reason: the paper says the switching argument uses the code family only through the degree bound (p. 6); every code family of Definition 3.1 qualifies
--   - generalization: Phi normalized (p. 23) → any list DNF with listWidth at most W; reason: repeated literals only increase the literal count and contradictory terms are never satisfied
--   - encoding: data entries off the secret are independent fair bits → a uniform data table whose entry at the secret is unused; reason: the same law
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 6.1, Eq. (6.1), p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_Light
import Definitions.Def_MantriCVQ_Pr
import Definitions.Def_MantriCVQ_binomLe
import Definitions.Def_MantriCVQ_listWidth

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

/-- **Theorem 6.1** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 6.1, Eq. (6.1), p. 23 (PDF p. 25)): for a DNF `Φ` of width at most
`W` on `K` independent blocks of dimension `m`, every `t ≥ 0`, every `z` and every `1 ≤ ℓ ≤ W`, the
probability that `Φ` accepts `ρ(z)` and at least `ℓ` blocks are light for the first satisfied term is at
most `binom(K, ℓ) (2W/ℓ)^ℓ binom(m, ≤dt)^ℓ 2^{-mℓ}`, and the event is empty if `ℓ > K`.

**Formalization Note** The first satisfied term is taken in list order. `Φ` need not be normalized (a
generalization). Only the degree bound of the code family is used. -/
theorem theorem_6_1 {d : ℕ} (C : CodeDeg d) {K m W t ℓ : ℕ} (hm : 0 < m) (h8 : 8 ∣ m)
    (Φ : DNF (Fin K × Addr [m])) (hΦ : listWidth Φ ≤ W) (z : Fin K → Bool)
    (hℓ : 1 ≤ ℓ) (hℓW : ℓ ≤ W) :
    Pr (fun s : Fin K → Seed [m] => lightEvent C.code t ℓ Φ z s) ≤
        (K.choose ℓ : ℝ) * ((2 * W : ℝ) / ℓ) ^ ℓ * (binomLe m (d * t) : ℝ) ^ ℓ *
          (2 : ℝ) ^ (-((m : ℝ) * ℓ)) ∧
      (K < ℓ → ∀ s : Fin K → Seed [m], ¬ lightEvent C.code t ℓ Φ z s) := by sorry

end MantriCVQ
