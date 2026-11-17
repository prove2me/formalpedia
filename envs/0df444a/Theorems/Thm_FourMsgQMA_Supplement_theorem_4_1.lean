-- Prove2me | Theorems.Thm_FourMsgQMA_Supplement_theorem_4_1
-- name    : FourMsgQMA.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:32:22.112661+00:00
-- url     : https://prove2.me/theorems/59bf85c0-fd55-4fab-921f-9688d70acff7
-- title:
--   Theorem 4.1 — the four-message batch compiler
-- statement:
--   This is Theorem 4.1 (four-message batch compiler) in the pinned-down version requested by the operator.
--
--   Let $L$ be a QMA promise problem with verification family $F$. Let $\Pi_0$ be a base protocol with negligible base soundness at every admissible resource bound (Definition 3.7) and completeness error a negligible $\varepsilon_0$, satisfying the base size bounds; let $\mathrm{SC}$ be a block commitment with index hiding, statistical extraction consistency (Definitions 3.17, 3.18), uniform statistical completeness and succinctness; let $B$ be a vector BARG with index hiding and somewhere extraction (Definitions 3.20, 3.21), uniform statistical completeness and efficiency; and let the FHE be uniformly correct, compact and IND-CPA secure (Definitions 3.14, 3.15). Then, for every valid choice of the circuits and bounds the construction leaves open, the construction of §4.2:
--
--   1. is **semi-adaptively sound** (Definition 3.5): $\Pr[b=1\wedge x_{i^*}=x^*]\le\mathrm{negl}(\lambda)$ for every fixed $i^*\in[k]$ and $x^*\in L_{\mathrm{no}}$ chosen before setup;
--   2. is **statistically complete**: rejection is negligible for every yes-batch and every honest resource $\bigotimes_{i\in[k]}\omega_i$;
--   3. has every message of length at most $p(\lambda,T,\log(k+1))$;
--   4. uses $N(\lambda,T)$ witness copies per real entry, exactly those of the base protocol;
--   5. sends one base key (the public part of a single run of $\Pi_0.\mathrm{Gen}(1^\lambda,T)$) and $d+1$ FHE public keys, $d=\lceil\log_2k\rceil$.
--
--   This compiler aggregates $k$ base executions into one four-message argument with communication polylogarithmic in $k$.
--
--   Differences from the source:
--   - reading: "Π0 satisfies Definition 3.7 with negligible error" → baseSoundAt: negligible acceptance for every fixed no-instance sequence of polynomial length, every polynomially bounded resource bound T(λ) ≥ t_L(x_λ) and every IsQPT adversary; reason: the batch runs one Gen(1^λ, T) for a common bound T on the entries (p.26); Definition 3.7's Gen takes T
--   - reading: "Assume also the completeness and succinctness properties used above" → base completeness with negligible error ε0 at every T ≥ t_L(x) (baseCompleteAt), BaseProtocol.Bounded, uniform statistical completeness (secStatComplete) and Succinct for SC, uniform statistical completeness (vbStatComplete) and Efficient for B, FHE.Compact; reason: §4.3 (p.29) uses exactly ε0, ε_sc, ε_B, ε_fhe and the size bounds of §§3.9–3.11
--   - reading: "the construction in Section 4.2" → batchCompiler P I for every implementation choice I with I.Valid (circuits for V(x_i, ·, µ, c, z), G_{a,b} and R_path computing their functions, depth ≤ the common level L on the inputs they are evaluated on (an entry with t_L(x) ≤ T, a challenge of the prescribed length, a base tape and a secret key of the prescribed lengths), polynomial-time compilation, polynomial bounds, declared lengths fitting the honest encodings on the views the honest prover can have); reason: the paper leaves these circuits and bounds implicit; the statement for every valid choice is the stronger reading
--   - reading: statistical completeness, rejection ≤ kε0 + ε_sc + ε_B + (d+1)ε_fhe (p.29) → BatchArg.Complete: for every polynomial bound B′ a negligible ν bounding rejection for every λ, every T ≤ B′(λ), every yes-batch with 1 ≤ k ≤ B′(λ) and t_L(x_i) ≤ T, and every ρ_i ∈ W_Q(x_i, 2/3); reason: admissible batches are polynomial, so the displayed sum is negligible; §3.3's overwhelming acceptance completeness
--   - encoding: the semi-adaptive game of Definition 3.5 → BatchArg.SemiAdaptiveSound: polynomial k ≥ 1 and T, fixed i* ∈ [k] and x* ∈ L_no with t_L(x*) ≤ T; the adversary's last answer is pack [pack X, a2]; it wins iff Dec(X, v2, a2) = 1 and x_{i*} = x*; reason: Lean representation of the game; Dec rejects a batch of the wrong size
--   - encoding: message length poly(λ, T, log k) → BatchArg.ShortMessages: one polynomial p with every message ≤ p(λ, T, ⌈log₂(k+1)⌉) and answers longer than that rejected; the honest answers are bounded on admissible batches (t_L(x_i) ≤ T) and on the views the honest prover can have; reason: ⌈log₂(k+1)⌉ covers k = 1; §3.3 batch communication (p.12)
--   - encoding: "one base key and d + 1 FHE keys", "no additional witness copies beyond those of the base protocol for each real entry" → the first field of M1 is the public output of one run of Π0.Gen(1^λ, T); the FHE public-key list has length ⌈log₂ k⌉ + 1; copies = N(λ, T) of the base; honest resource ⊗_{i∈[k]} ρ_i^{⊗N(λ,T)}; reason: Lean form of these clauses
--   - encoding: honest resources ω_i ∈ W_0(x_i), QPT adversaries, [k] = {1, …, k} → N(λ, T) copies of ρ_i ∈ W_Q(x_i, 2/3) on the i-th region of the honest core; IsQPT strategies; 1-based indices, padded entries copy x_1; reason: pinned-down model of the base mission (threshold 2/3, p.10)
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 4.1, p.29 (PDF 31); §4.2–4.3, pp.26–29 (PDF 28–31)

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_BatchCompiler
import Definitions.Def_FourMsgQMA_Supplement_StatComplete

namespace FourMsgQMA

namespace Supplement

open QAlgorithms.Complexity TightPQRepetition.Main

/-- **Theorem 4.1** (Four-message batch compiler), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.29 (PDF 31): "Assume that `Π₀` satisfies Definition 3.7 with negligible error,
that SC satisfies index hiding and extraction consistency (Definitions 3.17 and 3.18), that B
satisfies index hiding and adaptive extraction (Definitions 3.20 and 3.21), and that FHE satisfies
uniform correctness and post-quantum IND-CPA security (Definitions 3.14 and 3.15). Assume also the
completeness and succinctness properties used above. Then the construction in Section 4.2 is a
four-message classical argument satisfying semi-adaptive soundness (Definition 3.5), with
statistical completeness and message length poly(λ, T, log k) (the properties in Section 3.3). It
uses one base key and d + 1 FHE keys and requires no additional witness copies beyond those of the
base protocol for each real entry."

Let `L` be a QMA promise problem with verification family `F`. Assume negligible base soundness at
every admissible resource bound (Definition 3.7), index hiding and statistical extraction
consistency of `SC` (Definitions 3.17, 3.18), index hiding and somewhere extraction of `B`
(Definitions 3.20, 3.21), uniform correctness and IND-CPA security of the FHE (Definitions 3.14,
3.15), and the completeness and succinctness properties of §4.3: base completeness with negligible
error `ε₀` at every admissible bound, the base size bounds, uniform statistical completeness (negligible
bad-setup probability `ε_sc`) and succinctness of `SC`, uniform statistical completeness (`ε_B`) and
efficiency of `B`, and FHE compactness. Then for every valid choice
of the circuits and bounds the construction leaves open, the §4.2 construction

1. is semi-adaptively sound (Definition 3.5);
2. is complete with negligible error for every yes-batch and every honest resource `⊗_i ω_i`;
3. has every message of length at most `p(λ, T, ⌈log₂(k + 1)⌉)`;
4. uses `N(λ, T)` witness copies per real entry, those of the base protocol;
5. sends one base key, the public part of a single run of `Π₀.Gen(1^λ, T)`, and `d + 1` FHE public
   keys, `d = ⌈log₂ k⌉`. -/
theorem theorem_4_1 (L : PromiseProblem) (F : QMAFamily) (hLF : IsQMAVerifierFor L F)
    (P : BCPrims) (I : BCImpl)
    (hbase : baseSoundAt P.base L F) (hhid : P.sc.IndexHiding) (hext : P.sc.StatExtractConsistent)
    (hvb : P.vb.Secure) (hcor : P.fhe.UniformlyCorrect) (hcpa : P.fhe.INDCPA)
    (ε0 : ℕ → ℝ) (hε0 : Negligible ε0) (hbc : baseCompleteAt P.base L F ε0) (hbb : P.base.Bounded F)
    (hscc : secStatComplete P.sc) (hscs : P.sc.Succinct) (hvbc : vbStatComplete P.vb)
    (hvbe : P.vb.Efficient) (hcmp : P.fhe.Compact) (hI : I.Valid P F) :
    (batchCompiler P I).SemiAdaptiveSound L F ∧ (batchCompiler P I).Complete L F ∧
      (batchCompiler P I).ShortMessages F ∧ (∀ lam T, (batchCompiler P I).copies lam T = P.base.copies lam T) ∧
      ∀ (lam k T : ℕ) (r : Bits),
        let m1 := unpack ((batchCompiler P I).firstMsg lam k T r).1
        m1.headD [] = (P.base.gen lam T (r.take (P.base.genCoins lam T))).1 ∧
          (unpack (m1.getD 2 [])).length = clog2 k + 1 := by sorry

end Supplement

end FourMsgQMA
