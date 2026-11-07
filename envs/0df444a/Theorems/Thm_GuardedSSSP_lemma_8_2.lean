-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_8_2
-- name    : GuardedSSSP.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:24.64164+00:00
-- url     : https://prove2.me/theorems/396078ce-6d1d-429c-90c2-195545538ce8
-- title:
--   Lemma 8.2 — stripping one threshold: $\psi(R(T_j))\le R(T_{j-1})$ and $L_{d-2}(x)\le A_0$ at $d=D_*(x)$
-- statement:
--   Let $T_4\ge16$, $R(y)=256(y+1)^2$, $A_0=R(T_4)$ and $\psi(y)=\log_2(4+y)$.
--
--   1. For every $j\ge5$, $\psi(R(T_j))\le R(T_{j-1})$.
--   2. For every real $x\ge X_4$, with $d=D_*(x)$, every iterate $L_i(x)$ with $i\ge d-2$ satisfies $L_i(x)\le A_0$.
--
--   At the maximal legal generation, all iterates beyond depth $d-2$ are bounded by a constant depending only on $T_4$.
--
--   Differences from the source:
--   - generalization: the fixed base threshold T₄ of Specification A.1 ("a sufficiently large integer T₄ ≥ 16") → every natural T₄ ≥ 16; reason: the statement for every T₄ ≥ 16 specializes to the paper's fixed T₄
--   - encoding: If d = D∗(x) → for every real x ≥ X₄ with d = D∗(x); reason: D∗(x) is defined for x ≥ X₄ (display (13))
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 8.2, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy
import Definitions.Def_GuardedSSSP_Thresholds

namespace GuardedSSSP

/-- **Lemma 8.2** (Stripping one threshold), p.18 (PDF p.19).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Let R(y) = 256(y + 1)² and A₀ = R(T₄). For j ≥ 5,
ψ(R(T_j)) ≤ R(T_{j−1}). (31) If d = D∗(x), then L_{d−2}(x) ≤ A₀, and all later iterates are at most A₀."

For every base threshold `T₄ ≥ 16`:
1. (31) for every `j ≥ 5`;
2. for every real `x ≥ X₄`, with `d = D*(x)`, every iterate `L_i(x)` with `i ≥ d − 2` is at most `A₀`.

**Formalization Note.** `D*(x)` is defined for `x ≥ X₄` (display (13)), so the second clause assumes
`x ≥ X₄`; there `d ≥ 4` and `d − 2 ≥ 2`. The base threshold is any `T₄ ≥ 16`. -/
theorem lemma_8_2 (T4 : ℕ) (hT4 : 16 ≤ T4) :
    (∀ j : ℕ, 5 ≤ j → psi (R (Tpaper T4 j)) ≤ R (Tpaper T4 (j - 1))) ∧
    (∀ x : ℝ, (X4 T4 : ℝ) ≤ x → ∀ i : ℕ, Dstar T4 x - 2 ≤ i → L i x ≤ A0 T4) := by sorry

end GuardedSSSP
