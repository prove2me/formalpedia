-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_D_1
-- name    : InteractionElim.Main.lemma_D_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:20:31.568883+00:00
-- url     : https://prove2.me/theorems/9ec0e607-da9d-4dc8-901c-662423f30005
-- title:
--   Lemma D.1 — translate-cover lesson: $b+\log_2(r+1)+O(1)$ bits from $t=Qx+d$ leave a cell with root certificates $\le2T$
-- statement:
--   Fix a full-row-rank binary matrix $Q$ ($h$ rows) with $\operatorname{row}Q=W\le\mathbb F_2^r$, and a nonempty $W^\perp$-saturated cell $C$. Write $b=r-\log_2|C|$ and $T=|C|^{-1}\sum_{z\in C}\tau(z,C)$. Suppose the expert knows $t=Qx+d$ and the agent will learn the offset $d$ before executing this block. Then there is a fixed public encoding of $t$ using at most $b+\log_2(r+1)+O(1)$ bits such that, upon learning $d$, the agent obtains a cell containing $x$ with every root certificate at most $2T$. A singleton can instead be taught exactly.
--
--   Formally: there is a universal $C_0>0$ such that for all such $r,h,Q,C$ there are a length $\ell\le b+\log_2(r+1)+C_0$, an encoder $\mathrm{enc}:\mathbb F_2^h\to\{0,1\}^\ell$ and a decoder $\mathrm{dec}(\text{code},d)$ returning a cell, such that for all $x\in\mathbb F_2^r$ and $d\in\mathbb F_2^h$ the cell $\mathrm{dec}(\mathrm{enc}(Qx+d),d)$ contains $x$, every root $z$ of it has $\tau(z,\text{cell})\le2T$, and if $|C|=1$ the cell is $\{x\}$.
--
--   The expert encodes only its own record; the agent removes the offset after the earlier stages are executed.
--
--   Differences from the source:
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - reading: 'a fixed public encoding of t using at most b + log2(r + 1) + O(1) bits' → a fixed-length code enc : F_2^h → {0,1}^ℓ with ℓ ≤ b + log2(r+1) + C0, and a decoder taking the code and d; reason: the proof sends a fixed-length index; a prefix-free code of maximal length ℓ pads to fixed length ℓ
--   - reading: 'A singleton can instead be taught exactly' → if |C| = 1 the decoded cell is exactly {x} (same encoding); reason: for a singleton, 2T = 0 and the main clause already forces the cell {x}
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 37, Lemma D.1

import Mathlib
import Definitions.Def_InteractionElim_Main_Certificate

open scoped BigOperators

namespace InteractionElim.Main

theorem lemma_D_1 :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (r h : ℕ) (Q : Matrix (Fin h) (Fin r) (ZMod 2)) (C : Finset (Fin r → ZMod 2)),
        Q.rank = h → C.Nonempty →
        Saturated (C : Set (Fin r → ZMod 2)) (orth (Submodule.span (ZMod 2) (Set.range Q))) →
        ∃ (ℓ : ℕ) (enc : (Fin h → ZMod 2) → Fin ℓ → Bool)
          (dec : (Fin ℓ → Bool) → (Fin h → ZMod 2) → Finset (Fin r → ZMod 2)),
          (ℓ : ℝ) ≤ ((r : ℝ) - Real.logb 2 C.card) + Real.logb 2 ((r : ℝ) + 1) + C0 ∧
          ∀ (x : Fin r → ZMod 2) (d : Fin h → ZMod 2),
            x ∈ dec (enc (Q.mulVec x + d)) d ∧
            (∀ z ∈ dec (enc (Q.mulVec x + d)) d,
              tau z (dec (enc (Q.mulVec x + d)) d : Set (Fin r → ZMod 2)) ≤
                2 * ((1 / (C.card : ℝ)) * ∑ y ∈ C, tau y (C : Set (Fin r → ZMod 2)))) ∧
            (C.card = 1 → dec (enc (Q.mulVec x + d)) d = {x}) := by sorry

end InteractionElim.Main
