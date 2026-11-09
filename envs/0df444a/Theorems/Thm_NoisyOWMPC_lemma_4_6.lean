-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_4_6
-- name    : NoisyOWMPC.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:50:16.053971+00:00
-- url     : https://prove2.me/theorems/ddd8a036-b1d5-433e-8709-512d5329f53c
-- title:
--   Lemma 4.6 — noise preservation implies non-degradation
-- statement:
--   Let $\mathbf C=(C_1,\dots,C_k)$ be a product broadcast channel and suppose it satisfies noise preservation with bits $\beta$. Then for every receiver $i$,
--   $$C_i\not\preceq\mathbf C_{-i},$$
--   that is, there is no stochastic map $K$ with $C_i=\mathbf C_{-i}K$. For $k=1$ the channel $\mathbf C_{-i}$ has a single output, so the conclusion says that $C_i$ is nonconstant.
--
--   Non-degradation is what the access test needs, and it shows that every noise-preserving channel has nonconstant marginals, a hypothesis of Theorem 5.25.
--
--   Differences from the source:
--   - encoding: C_{−i} for k = 1 is 'the trivial channel with one output' → the product over the empty index set, a type with one element; reason: the paper's own convention after the proof (p.20)
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 4.6, p.20

import Mathlib
import Definitions.Def_NoisyOWMPC_NoisePreserving

namespace NoisyOWMPC

/-- **Lemma 4.6 (Noise preservation implies non-degradation)** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Lemma 4.6, p.20): "If a product broadcast channel `C`
satisfies noise preservation, then it also satisfies non-degradation, namely, `C_i ⋠ C_{−i}` for
every receiver `i`."

**Formalization Note** `C_{−i}` has output `∏_{j ≠ i} Y_j`; for `k = 1` this product has one
element, so the conclusion says that `C_i` is not a constant channel (p.20). -/
theorem lemma_4_6 {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool) (hβ : NoisePreserving C β) (i : Fin k) :
    ¬ Degraded (C i).P (minusP C i) := by sorry

end NoisyOWMPC
