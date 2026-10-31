-- Prove2me | Theorems.Thm_MayersBC_bcjl_insecure
-- name    : MayersBC.bcjl_insecure
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T16:00:25.522778+00:00
-- url     : https://prove2.me/theorems/f6b992ec-f802-486c-b43c-90a5f4b87928
-- title:
--   Section d, p.9 — the BCJL protocol is insecure: if it conceals the bit within $\varepsilon$, Alice opens $1$ with probability $\ge 1 - \varepsilon' - 4\sqrt\varepsilon$
-- statement:
--   Consider the BCJL bit commitment on $n$ photons with a linear code $C \subseteq \{0,1\}^n$, a string $r \in \{0,1\}^n$, and an arbitrary test $T_b(\theta, c, \hat\theta, \hat c)$ that Bob applies to Alice's opening $(\theta, c)$ and his own measurement outcome $(\hat\theta, \hat c)$. Let $\rho_0, \rho_1$ be the honest commitment states. Let $\varepsilon, \varepsilon'$ be real numbers and assume:
--
--   1. (security against Bob) every guess of the bit from the photons has $|\mathrm{PE} - \tfrac12| \le \varepsilon$;
--   2. (correctness for $b=1$) an honest opening of $1$ is accepted with probability $\Pr(T_1(W^{(1)}) = ok) \ge 1 - \varepsilon'$.
--
--   Then Alice can prepare one pure state $\varphi$ of her register (indexed by the openings $(\theta, c)$) and the $n$ photons, whose reduced state on the photons is the honest $\rho_0$, and measure her register alone after the commit with $N_0$ or $N_1$, such that the opening of $0$ is accepted with exactly the honest probability $\Pr(T_0(W^{(0)}) = ok)$, and the opening of $1$ is accepted with probability at least
--
--   $$
--   \Pr\big(T_1(W^{(1)}) = ok\big) - 4\sqrt{\varepsilon}
--   \qquad\text{and at least}\qquad
--   1 - \varepsilon' - 4\sqrt{\varepsilon} .
--   $$
--
--   With the paper's values $\varepsilon = \varepsilon' = 1/25$ the last bound is $1 - \tfrac1{25} - \tfrac45 = \tfrac4{25}$: a dishonest Alice changes her mind with probability at least $4/25$, so the protocol is not binding.
--
--   **Formalization Note** If no codeword has $c \odot r = 1$, the honest commitment to $1$ is the zero operator; the statement still holds as written (the honest probability is $0$ and correctness forces $\varepsilon' \ge 1$), so no hypothesis excludes this case.
--
--   Differences from the source:
--   - generalization: ε = ε′ = 1/25, giving 1 − ε′ − 4√ε = 4/25 → arbitrary real ε, ε′ with the bound 1 − ε′ − 4√ε; reason: the proof uses no property of the values; at ε = ε′ = 1/25 the bound is 4/25
--   - generalization: a linear code C (with some required properties) → any ZMod 2-submodule C of (ZMod 2)^n; reason: the properties are never used, and every code with them is a linear code
--   - generalization: the conclusion Pr(T1(Y) = ok | Φ = φ0) ≥ 1 − ε′ − 4√ε → also the clause Pr(T1(W^(1)) = ok) − 4√ε ≤ cheatAccept φ N1 (bobPOVM n) T 1, which needs no correctness; reason: it is the p.9 display combined with Pr(T1(Y) = ok | Φ = φ1) = Pr(T1(W^(1)) = ok), proved before correctness is used; the final clause is kept as well
--   - reading: (C, r) fixed, suppressed in the notation (p.4) → C and r are parameters, and Bob's criterion and correctness are assumed for that (C, r); reason: the analysis of pp.4–9 is done for (C, r) fixed, and ρ0, ρ1 are the states for that (C, r)
--   - reading: Bob's best guess X satisfies |PE − 1/2| ≤ ε → IsConcealing ε ρ0 ρ1 (every binary guess on the photon space); reason: a guess from any measurement is a binary measurement; the best guess has PE ≤ 1/2 and swapping outcomes maps PE to 1 − PE, so the conditions are equivalent
--   - encoding: Pr(T1(Y) = ok | Φ = φ1) ≥ 1 − ε′ 'if the protocol is correct' → 1 − ε′ ≤ bcjlHonestAccept C r T 1; reason: on φ1 Alice's measurement reproduces the honest W^(1) (p.5), so the two probabilities are equal
--   - encoding: Alice's system A, her measurements M_b^(A), Bob's measurement, bits and bases → a register indexed by Opening n (first tensor factor), POVMs N0, N1 on it, Bob's bobPOVM n, bits in ZMod 2, bases as Bool, the test as an arbitrary predicate with (C, r) suppressed, joint probabilities ⟨φ|N_w ⊗ E_y|φ⟩; reason: conventions that change no instance; the measurements commute (p.5), so the joint law is order-independent; the existential over a fixed register is the stronger form
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.9 (with the criterion of p.7 and the attack of p.5)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_MayersBC_Opening
import Definitions.Def_MayersBC_IsConcealing
import Definitions.Def_MayersBC_cheatAccept
import Definitions.Def_MayersBC_bcjlDensity
import Definitions.Def_MayersBC_bobPOVM
import Definitions.Def_MayersBC_bcjlHonestAccept
open QAlgorithms

namespace MayersBC

/-- Mayers, *The Trouble with Quantum Bit Commitment*, arXiv:quant-ph/9603015v3, section d,
pp.7–9: "We show that if the protocol is secure against Bob, then it is not secure against
Alice" (p.7), concluded on p.9: "If the protocol is correct, we can also assume that
Pr(T1(Y) = ok | Φ = φ1) ≥ 1 − ε′ where ε′ = 1/25. Therefore, we obtain that
Pr(T1(Y) = ok | Φ = φ0) ≥ 1 − ε′ − 4√ε = 4/25. This concludes the proof that the BCJL protocol
is insecure."

For every `n`, every linear code `C ⊆ {0,1}^n`, every `r`, every test `T_b(θ, c, θ̂, ĉ)` and all
`ε, ε'`: if Bob's criterion holds (`|PE − ½| ≤ ε` for every guess of `b` from the photons, between
`ρ_0` and `ρ_1`) and the protocol is correct for `b = 1` (`Pr(T_1(W^{(1)}) = ok) ≥ 1 − ε'`), then
Alice can prepare one pure state `φ` of her register and the `n` photons, whose reduced state on
the photons is the honest `ρ_0`, and measure her register alone with `N_0` or `N_1` after the
commit, such that the opening of `0` is accepted with exactly the honest probability and the
opening of `1` with probability at least `Pr(T_1(W^{(1)}) = ok) − 4√ε` and at least
`1 − ε' − 4√ε`. At the paper's values `ε = ε' = 1/25` the last bound is
`1 − 1/25 − 4·(1/5) = 4/25`.

**Formalization Note.** Alice's register is indexed by `Opening n` (the pairs `(θ, c)`), the first
tensor factor; her announced `(θ, c)` is the outcome of `N_b`; Bob measures with the honest
`bobPOVM n`. `ε` and `ε'` are free parameters (the paper fixes `1/25`); the code needs no
"required properties". If no codeword has `c ⊙ r = 1` the honest commitment to `1` is the zero
operator and the statement still holds as written (no extra hypothesis). -/
theorem bcjl_insecure (n : ℕ) (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (r : Fin n → ZMod 2)
    (T : ZMod 2 → Opening n → Opening n → Prop) (ε ε' : ℝ)
    (hBob : IsConcealing ε (bcjlDensity C r 0) (bcjlDensity C r 1))
    (hcorrect : 1 - ε' ≤ bcjlHonestAccept C r T 1) :
    ∃ φ : EuclideanSpace ℂ (Opening n × (Fin n → ZMod 2)), IsState φ ∧
      traceLeft (pureDensity φ) = bcjlDensity C r 0 ∧
      ∃ N0 N1 : Opening n → Matrix (Opening n) (Opening n) ℂ, IsPOVM N0 ∧ IsPOVM N1 ∧
        cheatAccept φ N0 (bobPOVM n) T 0 = bcjlHonestAccept C r T 0 ∧
        bcjlHonestAccept C r T 1 - 4 * Real.sqrt ε ≤ cheatAccept φ N1 (bobPOVM n) T 1 ∧
        1 - ε' - 4 * Real.sqrt ε ≤ cheatAccept φ N1 (bobPOVM n) T 1 := by sorry

end MayersBC
