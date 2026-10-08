-- Prove2me | Theorems.Thm_GOSNIZK_CircuitSound_lemma_5
-- name    : GOSNIZK.CircuitSound.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:08.138996+00:00
-- url     : https://prove2.me/theorems/e3e7bb4c-0733-4c51-b041-fcbe1a60cf91
-- title:
--   Lemma 5 — in a cyclic group of order ≥ 4, b₂ = ¬(b₀ ∧ b₁) iff b₀ + b₁ + 2b₂ − 2 ∈ {0, 1}
-- statement:
--   Let $\mathcal M$ be a finite cyclic group with neutral element $0$ and generator $1$, and let $b_0,b_1,b_2\in\{0,1\}$, read as elements of $\mathcal M$.
--
--   1. If the order of $\mathcal M$ is at least $4$, then
--   $$b_2=\neg(b_0\wedge b_1)\iff b_0+b_1+2b_2-2\in\{0,1\}.$$
--   2. If the order of $\mathcal M$ is $3$, then
--   $$b_2=\neg(b_0\wedge b_1)\iff b_0+b_1+2b_2-2\in\{0,1\}\ \text{ and }\ b_0+b_1+b_2-1\in\{0,1\}.$$
--
--   The lemma turns a NAND gate into a statement that a single message lies in $\{0,1\}$, which a homomorphic proof commitment can prove. For order $3$ the first condition alone does not suffice: $b_0=b_1=b_2=0$ gives $-2=1$.
--
--   **Formalization Note** $\mathcal M$ is `ZMod N` (a finite cyclic group with generator $1$ is isomorphic to it, $1\mapsto1$); "order at least 4" is `4 ≤ N` and "order 3" is `N = 3`. Bits are booleans mapped to $0,1\in\mathbb Z/N\mathbb Z$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14, Lemma 5

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Scheme

namespace GOSNIZK.CircuitSound

/-- Lemma 5 (Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive Zero-Knowledge*, J. ACM
59(3) (2012), authors' version of March 7, 2011, p. 14). The finite cyclic group `M` with generator
`1` is `ZMod N`; bits are read as `0, 1 ∈ ZMod N` via `ofBit`. If the order is at least 4,
`b₂ = ¬(b₀ ∧ b₁)` iff `b₀ + b₁ + 2b₂ − 2 ∈ {0, 1}`; if the order is 3, iff in addition
`b₀ + b₁ + b₂ − 1 ∈ {0, 1}`. -/
theorem lemma_5 (N : ℕ) (b₀ b₁ b₂ : Bool) :
    (4 ≤ N →
      (b₂ = !(b₀ && b₁) ↔
        (ofBit b₀ + ofBit b₁ + 2 * ofBit b₂ - 2 : ZMod N) ∈ ({0, 1} : Set (ZMod N)))) ∧
    (N = 3 →
      (b₂ = !(b₀ && b₁) ↔
        (ofBit b₀ + ofBit b₁ + 2 * ofBit b₂ - 2 : ZMod N) ∈ ({0, 1} : Set (ZMod N)) ∧
        (ofBit b₀ + ofBit b₁ + ofBit b₂ - 1 : ZMod N) ∈ ({0, 1} : Set (ZMod N)))) := by sorry

end GOSNIZK.CircuitSound
