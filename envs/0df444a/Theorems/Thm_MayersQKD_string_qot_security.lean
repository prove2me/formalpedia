-- Prove2me | Theorems.Thm_MayersQKD_string_qot_security
-- name    : MayersQKD.string_qot_security
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:58.148071+00:00
-- url     : https://prove2.me/theorems/c6b44fa1-0e73-416c-95fb-dbf96a0b432f
-- title:
--   §5, closing display, p.8 — security of STRING-QOT against Bob
-- statement:
--   Let $\delta,d,\rho$ be reals with $0\le\delta<0.12\,d$, $0<d\le1/2$ and $H(d)+\rho<1$, where $H$ is the binary entropy. Then there are a factor of security $\xi>0$ and an $n_0$ such that, for all $n\ge n_0$, all $r,m$ with $r+m\le\rho N$, where $N=\lfloor.24n\rfloor$, every attack by Bob in which $E_0$ and $E_1$ are honestly chosen, and every initial distribution on the string $B\in\{0,1\}^m$,
--
--   $$
--   I(B;V\mid Pass=1\wedge C=1)\times\Pr(Pass=1)\le2^{-\xi n}.
--   $$
--
--   Here $V$ is Bob's view at the end of the protocol, $Pass=1$ means that the test result is accepted, and $C=1$ means that Alice chose the set $E_1$, on which Bob's bases differ from hers. The information is in bits, for the law conditioned on $Pass=1\wedge C=1$.
--
--   This is the security of the string oblivious transfer against Bob: when he holds the wrong-basis set and passes the test, he learns almost nothing about $b$, whatever coherent measurement he performs.
--
--   **Formalization Note** The factor $\xi$ and the threshold $n_0$ depend only on $(\delta,d,\rho)$. On a null event the product is $0$. The paper's $\epsilon$ does not appear: the condition is the existence of $\epsilon$ with $\delta<\epsilon<0.12\,d$.
--
--   Differences from the source:
--   - reading: no list of conditions on δ, r, m → 0 ≤ δ < 0.12 d, 0 < d ≤ 1/2, H(d) + ρ < 1, r + m ≤ ρN; reason: the widest regime allowed by εn < dN/2 (Lemma 1), d > H⁻¹(1−(r+m)/N) − η (§8) and "an appropriate ε > δ" (§10), with 0.12 = .24/2 from N = ⌊.24n⌋
--   - reading: for any attack … there exists ξ > 0 (ξ after the attack, n left free) → ξ > 0 and n₀ chosen before n, r, m, the attack and the prior, the bound holding for n ≥ n₀; reason: read literally, a ξ chosen after an attack with a fixed n only says the product is below 1, so ξ is taken uniform over attacks and priors (the stronger reading); §8 and §10 are asymptotic ("except with negligible probability"), and the argument yields a polynomial factor in front of the exponential, hence n ≥ n₀
--   - generalization: Bob picks θ̂ uniformly (step 2) → θ̂ any function of a seed with any distribution; reason: a dishonest Bob need not be uniform; the honest choice is an instance
--   - generalization: E₀, E₁ honestly chosen → any rule depending on the seed, ŵ, R, θ that answers a valid pair; reason: every honest rule, including the uniformly random one through the seed, is an instance
--   - reading: step 6 when |T₀ − R| < N or |T₁ − R| < N is not treated → the protocol stops there and nothing depending on b is announced; the rule may stop only when no valid pair exists; reason: the printed step cannot be carried out
--   - encoding: any measurement into any sufficiently large space → finite-dimensional memory and finite outcome sets; reason: the range of M_ŵ has dimension at most 2ⁿ, and a countable final measurement is a limit of finite coarse-grainings
--   - encoding: quantum commitments on top of an unconditionally secure bit commitment scheme → the committed values are the classical θ̂ and ŵ; reason: the abstract and §1 assume the commitment secure
--   - encoding: the law given by the operators M_R, M_c, P_C of §6 → the law given by its probabilities; reason: M_R = 2⁻ⁿI and M_c = 2⁻¹I are printed as if squared; (9) confirms the probabilities
--   - encoding: I(B;V|·) undefined on an event of probability 0 → the value 0; reason: C is independent of Pass, so the event is null exactly when Pr(Pass = 1) = 0, and the product is then 0
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §5, closing display, p.8

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_transcript

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §5, closing display, p.8: the security of STRING-QOT against
Bob. For any attack where `E₀` and `E₁` are honestly chosen there is a factor of security `ξ > 0`
such that, for any initial distribution of probability on `B`,
`I(B; V | Pass = 1 ∧ C = 1) × Pr(Pass = 1) ≤ 2^(−ξn)`.

**Formalization Note.** The paper lists no regime. Here: `0 ≤ δ < 0.12 d`, `0 < d ≤ 1/2`,
`H(d) + ρ < 1` and `r + m ≤ ρN`, the widest regime its conditions allow: `εn < dN/2` (Lemma 1, with
`N = ⌊.24n⌋` and `δ < ε`) and `d` below `H⁻¹(1 − (r+m)/N)` (§8). The factor `ξ` and the threshold `n₀`
depend only on `(δ, d, ρ)`: they come before `n`, `r`, `m`, the attack and the prior. Logarithms are
base 2, and `I` is the information for the conditioned law, `0` on a null event (the product is
then `0`). Attacks: `MayersQKD.Attack`. -/
theorem string_qot_security (δ d ρ : ℝ) (hδ : 0 ≤ δ) (hδd : δ < 0.12 * d) (hd0 : 0 < d)
    (hd1 : d ≤ 1 / 2) (hρ : WildeQIT.binaryEntropy d + ρ < 1) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ r m : ℕ,
      ((r : ℝ) + m ≤ ρ * blockLen n) →
      ∀ (A : Attack n r m) (prior : WildeQIT.FinDist (Bits m)),
        secrecyInfo A δ prior * passProb A δ prior ≤ (2 : ℝ) ^ (-(ξ * n)) := by sorry

end MayersQKD
