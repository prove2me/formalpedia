-- Prove2me | Theorems.Thm_OracleStateHSP_Supplement_theorem_3_4
-- name    : OracleStateHSP.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:13:11.902297+00:00
-- url     : https://prove2.me/theorems/9e065d40-1947-4be2-9438-b511a48e7ab8
-- title:
--   Theorem 3.4 — HSP-Sampling framework: success $\ge 1-\delta$ with $\le 3(\lfloor\log_2|G/H|\rfloor+\lceil\log_2 1/\delta\rceil)$ sampler calls
-- statement:
--   Let $G = \mathbb Z_{M_1} \times \dots \times \mathbb Z_{M_n}$ be a finite abelian group, $H \le G$ the hidden subgroup and $\delta \in (0, 1]$. Run Algorithm 1 with failure probability $\delta$ (so $b = \lceil \log_2(1/\delta)\rceil$), an HSP-sampler with failure parameter $\tilde\delta = 1/2$ (Definition 3.1), an UPDATE (Definition 3.2) and a DUAL-SOLVER (Definition 3.3).
--
--   **Theorem.**
--
--   1. With probability at least $1 - \delta$, Algorithm 1 outputs a generating set for $H$: the set $S = \mathrm{DUAL\text{-}SOLVER}(S^\perp)$ it returns satisfies $\langle S \rangle = H$.
--   2. On every run of positive probability the loop stops by its own exit condition $t \ge 3(i + b)$, and
--      - the number of calls to HSP-SAMPLER is at most $3\big(\lfloor \log_2 |G/H| \rfloor + \lceil \log_2 \tfrac1\delta \rceil\big)$;
--      - the number of calls to UPDATE is at most $\lfloor \log_2 |G/H| \rfloor$;
--      - DUAL-SOLVER is called once.
--
--   The adaptive budget lets the algorithm stop after $O(\log|G/H| + \log(1/\delta))$ sampler calls without knowing $|H|$ in advance, an additive rather than multiplicative overhead in $\log(1/\delta)$.
--
--   **Formalization Note** The run of Algorithm 1 is the law of the list of sampler outputs; the number of sampler calls is its length, the number of UPDATE calls its number of non-END entries, and the output is one application of the DUAL-SOLVER to the data structure built by UPDATE. $\lfloor\log_2\cdot\rfloor$ is `Nat.log 2` and $\lceil\log_2(1/\delta)\rceil$ is the natural-number ceiling of `Real.logb 2 (1/δ)`.
--
--   Differences from the source:
--   - generalization: a StateHSP instance over G with hidden subgroup H → any subgroup H ≤ G, with no instance parameter; reason: Algorithm 1 uses the instance only through the sampler, whose specification refers to H alone; every instance has a hidden subgroup, so the statement specializes to it
--   - generalization: HSP-SAMPLER(S⊥, 1/2) called on the current data structure with fresh randomness → a kernel whose law may depend on the whole list of previous outputs, meeting Definition 3.1 at every history with ⟨outputs⟩ ≤ H⊥; reason: S⊥ is a function of the previous outputs, so the paper's sampler is such a kernel; the proof takes the supremum over all sampler outputs
--   - encoding: G ≅ Z_M1 × ⋯ × Z_Mn (eq. (10)), Ĝ labelled by tuples → CycProd n M = (l : Fin n) → ZMod (M l) with every M l ≥ 1; Ĝ is the same type, characters by eq. (11); reason: covers every finite abelian group up to isomorphism
--   - encoding: data structures encoding generating sets; deterministic routines UPDATE and DUAL-SOLVER → finite sets of labels; UPDATE and DUAL-SOLVER any functions meeting Definitions 3.2 and 3.3; reason: only the generated subgroups are specified on the page
--   - encoding: the while-loop of Algorithm 1 → recursion with the bound 3(|G| + b) + 1 on the number of iterations, plus the conclusion that every run of positive probability meets the loop's exit condition; reason: the bound only makes the recursion well-founded and is never reached
--   - encoding: numbers of calls to HSP-SAMPLER, UPDATE and DUAL-SOLVER → length of the output list, number of its non-END entries, and the single application of dual in the output; reason: these are exactly the calls the loop makes
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Theorem 3.4, p.20; Algorithm 1, p.21; Definitions 3.1–3.3, pp.19–20

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_IsHSPSampler
import Definitions.Def_OracleStateHSP_Supplement_IsUpdate
import Definitions.Def_OracleStateHSP_Supplement_IsDualSolver
import Definitions.Def_OracleStateHSP_Supplement_alg1Run
import Definitions.Def_OracleStateHSP_Supplement_foldUpdate

namespace OracleStateHSP

namespace Supplement

/-- **Theorem 3.4 (HSP-Sampling framework)** (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Theorem 3.4, p.20; Algorithm 1, p.21).
Let `G = Z_(M_1) × ⋯ × Z_(M_n)` be a finite abelian group with hidden subgroup `H ≤ G`, let
`δ ∈ (0, 1]`, let `samp` be an HSP-sampler with failure parameter `δ̃ = 1/2` (Definition 3.1),
`upd` an UPDATE (Definition 3.2) and `dual` a DUAL-SOLVER (Definition 3.3). Run Algorithm 1
(`alg1Run`), with `b = ⌈log₂(1/δ)⌉`. Then

1. with probability at least `1 − δ`, the output `DUAL-SOLVER(S⊥)` (with `S⊥` built by `UPDATE`
   from the sampler outputs) generates `H`;
2. on every run of positive probability the loop has stopped by its own exit condition
   (`t ≥ 3(i + b)`), the number of HSP-SAMPLER calls (`|hist|`) is at most
   `3(⌊log₂|G/H|⌋ + ⌈log₂(1/δ)⌉)`, and the number of UPDATE calls (non-END outputs) is at most
   `⌊log₂|G/H|⌋`. DUAL-SOLVER is called once, by construction of the output.

**Formalization Note.** `⌊log₂ x⌋` is `Nat.log 2`, `⌈log₂(1/δ)⌉` is `⌈Real.logb 2 (1/δ)⌉₊`
(as in `alg1Run`). The sampler's law may depend on the whole history (Definition 3.1 as
`IsHSPSampler`), so it is adversarial within the specification. The instance (state vector or
preparation unitary) enters only through `H` and the sampler, so it is not a parameter. -/
theorem theorem_3_4 {n : ℕ} {M : Fin n → ℕ} [∀ l, NeZero (M l)]
    (H : AddSubgroup (CycProd n M)) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (samp : List (Option (CycProd n M)) → PMF (Option (CycProd n M)))
    (hsamp : IsHSPSampler H (1 / 2) samp)
    (upd : Finset (CycProd n M) → CycProd n M → Finset (CycProd n M)) (hupd : IsUpdate upd)
    (dual : Finset (CycProd n M) → Finset (CycProd n M)) (hdual : IsDualSolver dual) :
    ENNReal.ofReal (1 - δ) ≤ (alg1Run samp δ).toOuterMeasure
        {hist | AddSubgroup.closure (dual (foldUpdate upd hist) : Set (CycProd n M)) = H} ∧
    ∀ hist ∈ (alg1Run samp δ).support,
      ¬ hist.length < 3 * ((hist.filter Option.isSome).length + ⌈Real.logb 2 (1 / δ)⌉₊) ∧
      hist.length ≤ 3 * (Nat.log 2 (Nat.card (CycProd n M ⧸ H)) + ⌈Real.logb 2 (1 / δ)⌉₊) ∧
      (hist.filter Option.isSome).length ≤ Nat.log 2 (Nat.card (CycProd n M ⧸ H)) := by sorry

end Supplement

end OracleStateHSP
