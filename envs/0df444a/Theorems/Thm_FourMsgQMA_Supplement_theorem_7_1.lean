-- Prove2me | Theorems.Thm_FourMsgQMA_Supplement_theorem_7_1
-- name    : FourMsgQMA.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:34:21.74391+00:00
-- url     : https://prove2.me/theorems/053cf13e-f9c4-40c2-bc88-aa5911d83495
-- title:
--   Theorem 7.1 — the imported short-key base
-- statement:
--   This is Theorem 7.1 (imported short-key base, [GKNV25, Theorem C.2]) in the pinned-down version requested by the operator.
--
--   Fix $\varepsilon\in(0,1)$ and assume $\mathrm{Hyp}(\varepsilon)$. Then every QMA promise problem $L$ with verification family $F$ has an **independent-challenge base** (Definition 3.8) that
--
--   1. is uniform and polynomially bounded, with challenge length $m\le\mathrm{poly}(\lambda,|x|,\log(T+1))$;
--   2. has a uniform challenge of exactly $\lambda+2$ bits ($c=(b,h,s)$);
--   3. has **short public and secret commitment keys**: $PK_0$ and the secret key in $r$ come from a key generator whose coins, key lengths and running time are $\mathrm{poly}(\lambda)$, independent of $x$ and $T$;
--   4. is complete with error $\mathrm{negl}(\lambda)$ for $N(\lambda,T)$ copies of any witness in $W_Q(x,2/3)$;
--   5. has selective soundness at most
--   $$
--   1-\lambda^{-2}+\mathrm{negl}(\lambda).
--   $$
--
--   This is the base of the six-message construction of Theorem 7.5; its inverse-polynomial gap $g=\lambda^{-2}$ enters the soundness bound there.
--
--   Differences from the source:
--   - reading: "the quantum-secure LWE assumption for the commitment scheme of [GKNV25]" → Hyp(ε) for the given ε ∈ (0, 1) (published FourMsgQMA.LWEHyp); reason: the same reading as the published base_protocol_bkl22 and corollary_5_15; the paper fixes no parameter family
--   - reading: "the preceding base with the prescribed post-hoc witness copies" → ∃ an ICBase with every stated property (pinned-down existential version); reason: the [GKNV25] commitment and the [ACGH20] post-hoc test are not reproduced in this paper; the existential form is the reading of the published base items
--   - reading: "It satisfies Definition 3.8 with short public and secret commitment keys" → IsUniform, Bounded (challenge ≤ p(λ, |x|, ⌈log₂(T+1)⌉)), challenge length exactly λ + 2, and ShortKeys: PK_0 = PK and the first component of r = SK for a key generator with coins, key lengths and time ≤ poly(λ), independent of x and T; reason: §7.1 (pp.49–50): "The key lengths and generation time are poly(λ), independent of N"; "PK_0 = PK_QC"; c = (b, h, s) ∈ {0,1}^{λ+2}
--   - encoding: "the prescribed post-hoc witness copies" → N(λ, T) copies, computable and ≤ poly(λ, T), of any ρ ∈ W_Q(x, 2/3); reason: QMA threshold 2/3 (p.10); the base mission's honest-resource convention
--   - encoding: 1 − λ^{-2} + negl(λ) → 1 − ((λ : ℝ)^2)⁻¹ + ν(λ), which is 1 + ν(0) at λ = 0; reason: Lean division convention; a single trivial point
--   - encoding: QPT adversaries, local resource T, selective soundness quantifiers → IsQPT strategies; T = t_L(x); for every polynomial length bound and fixed no-instance sequence ∃ negligible ν; reason: pinned-down model of the base mission (§3.1 quantifier convention)
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 7.1, p.50 (PDF 52); §7.1, pp.49–50 (PDF 51–52); Definition 3.8, pp.13–14

import Mathlib
import Definitions.Def_FourMsgQMA_LWEHyp
import Definitions.Def_FourMsgQMA_Supplement_ICBase

namespace FourMsgQMA

namespace Supplement

open QAlgorithms.Complexity

/-- **Theorem 7.1** (Imported short-key base), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.50 (PDF 52), pinned-down version (operator request): "Under the quantum-secure
LWE assumption for the commitment scheme of [GKNV25], the preceding base with the prescribed post-hoc
witness copies has completeness `1 − negl(λ)` and selective soundness at most `1 − λ^{-2} + negl(λ)`.
It satisfies Definition 3.8 with short public and secret commitment keys."

For every `ε ∈ (0, 1)`, under `Hyp(ε)`, every QMA promise problem `L` with verification family `F`
has an independent-challenge base (Definition 3.8) that is uniform and polynomially bounded, whose
challenge is a uniform string of length `λ + 2` (`c = (b, h, s)`), whose public setup and secret key
come from a key generator with keys and generation time `poly(λ)` independent of `x` and `T`, that is
complete with error `negl(λ)` for `N(λ, T)` copies of any witness in `W_Q(x, 2/3)`, and whose
selective soundness is at most `1 − λ^{-2} + negl(λ)`.

**Formalization Note** "The quantum-secure LWE assumption for the commitment scheme of [GKNV25]" is
read as `Hyp(ε)`; `T = t_L(x)`; the bound `λ^{-2}` is `((λ : ℝ)^2)⁻¹`, which Lean evaluates to `0`
at `λ = 0` (a single trivial point). -/
theorem theorem_7_1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hLWE : LWEHyp ε)
    (L : PromiseProblem) (F : QMAFamily) (hLF : IsQMAVerifierFor L F) :
    ∃ B : ICBase, B.IsUniform ∧ B.Bounded F ∧ B.ShortKeys ∧
      (∀ lam m T, B.chalLen lam m T = lam + 2) ∧ B.Complete L F ∧
      B.Sound L F (fun lam => 1 - ((lam : ℝ) ^ 2)⁻¹) := by sorry

end Supplement

end FourMsgQMA
