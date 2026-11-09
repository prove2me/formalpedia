-- Prove2me | Theorems.Thm_NoisyOWMPC_theorem_3_4
-- name    : NoisyOWMPC.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:00:06.0504+00:00
-- url     : https://prove2.me/theorems/18346d1c-2aac-4a14-bcbe-ca4a6a469232
-- title:
--   Theorem 3.4 — injective one-way functions from iO and one-way functions (Bitansky–Paneth–Wichs)
-- statement:
--   If one-way functions exist and an indistinguishability obfuscator (Definition 3.2) exists, then there is an injective one-way function in the sense of Definition 3.3: an efficiently computable keyed family that is one-way against nonuniform polynomial-size inverters and injective except with negligible probability over the key.
--
--   This result of [BPW16, Section 3] supplies the injective one-way function used by the seed-puncturing lemma.
--
--   Differences from the source:
--   - encoding: 'indistinguishability obfuscation for polynomial-size circuits exist' → ∃ O, IOScheme.IsIO O; reason: Definition 3.2 as formalized
--   - encoding: Definition 3.2: iO returns a circuit with 'polynomially bounded description'; obfuscations 'padded to a fixed public length' (p.21) → IOScheme carries a public length bound len(λ, n, s), polynomial and computable in polynomial time, on every obfuscated description; reason: every obfuscator with polynomially bounded descriptions has such a bound; it fixes the public transmission length
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 3.4, p.16 ([BPW16, Section 3])

import Mathlib
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_NoisyOWMPC_OWFExists

namespace NoisyOWMPC

/-- **Theorem 3.4 (Bitansky–Paneth–Wichs [BPW16, Section 3])** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Theorem 3.4, p.16): "If one-way functions and
indistinguishability obfuscation for polynomial-size circuits exist, then injective one-way
functions in the sense of Definition 3.3 exist." -/
theorem theorem_3_4 (hOWF : OWFExists) (hiO : ∃ O : IOScheme, O.IsIO) :
    ∃ F : KeyedFamily, F.IsInjOWF := by sorry

end NoisyOWMPC
