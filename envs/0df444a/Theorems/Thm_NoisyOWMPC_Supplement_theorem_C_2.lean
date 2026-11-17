-- Prove2me | Theorems.Thm_NoisyOWMPC_Supplement_theorem_C_2
-- name    : NoisyOWMPC.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:06:37.732704+00:00
-- url     : https://prove2.me/theorems/e2fa5dee-51e7-49b6-aadc-4bbd01118502
-- title:
--   Theorem C.2 — universal computational wiretap coding
-- statement:
--   Assume an indistinguishability obfuscator and one-way functions. Then:
--
--   1. For all channels $B : \mathcal X \to \mathcal Y$ and $E : \mathcal X \to \mathcal Z$ with a common nonempty finite input alphabet, there is an efficient wiretap coding scheme for one-bit messages that is correct over $B$ and computationally secure against $E$ (Definition C.1) if and only if
--   $$
--   B \not\preceq E ,
--   $$
--   that is, there is no stochastic map $K : \mathcal Z \to \mathcal Y$ with $B = EK$.
--   2. For every nonconstant $B$ there is a single efficient one-bit scheme, depending only on $B$ and correct over $B$, that is computationally secure against every channel $E : \mathcal X \to \mathcal Z$ (every finite $\mathcal Z$) with $B \not\preceq E$.
--   3. For every polynomial message length $\ell(\lambda)$ and every nonconstant $B$ there is a single efficient scheme for $\ell$-bit messages, correct over $B$ for every message, under which every two messages are computationally indistinguishable to every $E$ with $B \not\preceq E$.
--
--   The necessity direction of part 1 is information-theoretic; sufficiency uses an obfuscated program that releases the message on observations passing an access test for Bob. Part 2 gives a scheme universal in the eavesdropper's channel.
--
--   **Formalization Note** In parts 2 and 3 the scheme is fixed before $E$; its negligible security bounds may depend on $E$ and on the adversary. Adversaries are nonuniform polynomial-size circuit families.
--
--   Differences from the source:
--   - encoding: a pair of channels (B, E) on the same transmitted word → DMCs B : X → Y, E : X → Z with Nonempty X in the 'if and only if' part; reason: a channel is a randomized map on a nonempty alphabet; X = ∅ is undefined (no scheme exists, while with Y = ∅ ≠ Z no stochastic K exists either)
--   - encoding: assuming iO and one-way functions → an IOScheme O with IsIO and OWFExists as hypotheses; reason: the base mission's encoding of Definition 3.2 and 'one-way functions exist'
--   - reading: the scheme extends to messages of any polynomial length → for every polynomial ℓ and nonconstant B, one ℓ-bit scheme chosen before E, correct for every message, with every two messages indistinguishable to every E with B ⋠ E (uniformly over the pair); reason: p.57: 'for longer messages any two messages are indistinguishable by the same argument', and the universality paragraph applies to the same encoder
--   - generalization: messages of any polynomial length → every public polynomial parameter ℓ (PolyParam: polynomially bounded and computable from 1^λ in polynomial time); reason: every polynomial in λ is such a parameter, so the statement specializes to the source's
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem C.2, p.55 (necessity, p.55; sufficiency and universality, p.57)

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_WiretapScheme
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_NoisyOWMPC_OWFExists

namespace NoisyOWMPC.Supplement

/-- **Theorem C.2 (Universal computational wiretap coding)** (Ishai, Lu, Zafar, *Non-Interactive
Cryptography over Noisy Channels from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 3a9569fa…), Theorem C.2, p.55): "Assuming iO and one-way functions, a pair of
channels `(B, E)` admits a computationally secure wiretap coding scheme if and only if `B ⋠ E`.
Moreover, for every fixed nonconstant `B`, there is a single encoder–decoder pair depending only on
`B` that is secure for every fixed `E` with `B ⋠ E`. The scheme extends to messages of any
polynomial length."

For an iO scheme `O` and one-way functions existing:
1. for all DMCs `B : X → Y`, `E : X → Z` with a common nonempty finite input alphabet, an efficient
   one-bit scheme correct over `B` and secure against `E` (Definition C.1) exists iff `B ⋠ E`;
2. for every nonconstant `B` there is one efficient one-bit scheme, correct over `B`, that is secure
   against every `E : X → Z` (every finite `Z`) with `B ⋠ E`;
3. for every polynomial message length `ℓ` and every nonconstant `B` there is one efficient scheme
   for `ℓ`-bit messages, correct over `B` for every message, under which any two messages are
   indistinguishable to every `E` with `B ⋠ E`.

**Formalization Note** `B ⪯ E` is the published `Degraded` (`B = E K` for a stochastic `K : Z → Y`,
p.55). The input alphabet is nonempty (a channel is a randomized map on a nonempty alphabet; with
`X = ∅` and `Y = ∅ ≠ Z` no stochastic `K` exists while no scheme exists either). In parts 2 and 3
the scheme is chosen before `E`; the negligible bounds may depend on `E` and the adversary (p.57). A
polynomial message length is a public polynomial parameter (`PolyParam`). -/
theorem theorem_C_2 (O : IOScheme) (hO : O.IsIO) (hOWF : OWFExists) :
    (∀ (X Y Z : Type) [Fintype X] [Nonempty X] [Fintype Y] [Fintype Z] (B : DMC X Y) (E : DMC X Z),
      (∃ W : WiretapScheme X Y (fun _ => 1), W.IsEfficient ∧ W.Correct B ∧ W.SecureBit E) ↔
        ¬ Degraded B.P E.P) ∧
    (∀ (X Y : Type) [Fintype X] [Fintype Y] (B : DMC X Y), Nonconstant B →
      ∃ W : WiretapScheme X Y (fun _ => 1), W.IsEfficient ∧ W.Correct B ∧
        ∀ (Z : Type) [Fintype Z] (E : DMC X Z), ¬ Degraded B.P E.P → W.SecureBit E) ∧
    (∀ ℓ : ℕ → ℕ, PolyParam ℓ → ∀ (X Y : Type) [Fintype X] [Fintype Y] (B : DMC X Y),
      Nonconstant B → ∃ W : WiretapScheme X Y ℓ, W.IsEfficient ∧ W.Correct B ∧
        ∀ (Z : Type) [Fintype Z] (E : DMC X Z), ¬ Degraded B.P E.P → W.SecureMsg E) := by sorry

end NoisyOWMPC.Supplement
