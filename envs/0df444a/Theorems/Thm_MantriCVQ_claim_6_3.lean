-- Prove2me | Theorems.Thm_MantriCVQ_claim_6_3
-- name    : MantriCVQ.claim_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:03.231646+00:00
-- url     : https://prove2.me/theorems/38fbd78b-52bb-4cf0-b4a1-812bd139cd1a
-- title:
--   Claim 6.3 — counting secret tuples by rank
-- statement:
--   Let $\Phi$ be a DNF of width at most $W$ on $K$ height-one blocks of dimension $m$, a positive multiple of eight, let $t\ge0$, and let $I$ be a set of $\ell$ blocks with $1\le\ell\le W$. Fix the data tables $f=(f_i)_{i\in I}$ and the values of all leaves outside $I$. For a tuple $\tau=(\tau_i)_{i\in I}$ of secrets, the blocks of $I$ get the code tables $C_m(\tau_i,\cdot)$. Let $P(f)$ be the set of tuples for which $\Phi$ accepts the resulting input and every block of $I$ is light for the first satisfied term. Then
--   $$|P(f)|\le\Bigl(\frac W\ell\Bigr)^\ell\binom{m}{\le dt}^\ell.$$
--   The first factor counts the tuples with a given first satisfied term and the second the possible first satisfied terms. The count is the combinatorial heart of Theorem 6.1, which does not depend on the number of terms of $\Phi$.
--
--   Differences from the source:
--   - generalization: a code family of Definition 3.1 → any family with the degree condition (CodeDeg d); reason: the paper says the switching argument uses the code family only through the degree bound (p. 6); every code family of Definition 3.1 qualifies
--   - generalization: Phi normalized (p. 23) → any list DNF with listWidth at most W; reason: repeated literals only increase the literal count and contradictory terms are never satisfied, so normalized DNFs are a special case
--   - generalization: the blocks outside I are fixed by their projections and free values → arbitrary fixed values on the leaves outside I; reason: only their being fixed is used; the paper's values are a special case
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.3, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_Light
import Definitions.Def_MantriCVQ_binomLe
import Definitions.Def_MantriCVQ_experimentInput
import Definitions.Def_MantriCVQ_listWidth

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

open Classical in
/-- **Claim 6.3** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.3, p. 24 (PDF p. 26)): in the experiment of Claim 6.2, with the data
tables `f` of the blocks of `I` and all leaves outside `I` fixed, the number of secret tuples at which
`Φ` accepts and every block of `I` is light for the first satisfied term is at most
`(W/ℓ)^ℓ · binom(m, ≤dt)^ℓ`.

**Formalization Note** The setting is that of Theorem 6.1 (p. 23): `1 ≤ ℓ ≤ W`, and `m` is a positive
multiple of eight. The bound is real-valued. `Φ` need not be normalized (a generalization). -/
theorem claim_6_3 {d : ℕ} (C : CodeDeg d) {K m W t ℓ : ℕ} (hm : 0 < m) (h8 : 8 ∣ m)
    (Φ : DNF (Fin K × Addr [m])) (hΦ : listWidth Φ ≤ W)
    (I : Finset (Fin K)) (hI : I.card = ℓ) (hℓ : 1 ≤ ℓ) (hℓW : ℓ ≤ W)
    (f : Fin K → Bits m → Bool) (a : Fin K × Addr [m] → Bool) :
    (((Finset.univ : Finset (I → Bits m)).filter fun τ =>
        DNF.eval Φ (experimentInput C.code I τ f a) = true ∧
          ∃ T, firstSatTerm Φ (experimentInput C.code I τ f a) = some T ∧
            ∀ i : I, IsLight t T i (τ i)).card : ℝ) ≤
      ((W : ℝ) / ℓ) ^ ℓ * (binomLe m (d * t) : ℝ) ^ ℓ := by sorry

end MantriCVQ
