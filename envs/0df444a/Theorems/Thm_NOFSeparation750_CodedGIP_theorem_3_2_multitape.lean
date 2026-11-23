-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_theorem_3_2_multitape
-- name    : NOFSeparation750.CodedGIP.theorem_3_2_multitape
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T00:45:51.090038+00:00
-- url     : https://prove2.me/theorems/9e89573d-fac0-4951-9e66-4f83ae9c0fe9
-- title:
--   Theorem 3.2 with multi-tape effectiveness (Garcia–Stichtenoth compatible codes)
-- statement:
--   Theorem 3.2 of the source, with its effectiveness clause expressed through multi-tape Turing machines instead of multi-stack (TM2) programs.
--
--   Fix $k\ge2$ and an allowed $a$, so that $q=4^a$ satisfies $(32k)^2\le q\le(64k)^2$. Put $s=2^a$ and $r_j=(q-s)s^j$, and let $\mathbb F$ be a field with $q$ elements. Then there exist a family of code pairs $V_j,W_j\le\mathbb F^{r_j}$ with ordered bases, for $j\ge0$, and a bijection $\{0,1\}^{2a}\to\mathbb F$ with the following properties.
--
--   1. For every $j$, the pair $(V_j,W_j)$ is $(6/s,\,3/4)$-compatible for $k$-products:
--   $$V_j^{\odot k}\subseteq W_j,\qquad \dim V_j\ge \frac{6r_j}{s},\qquad \operatorname{dist}(W_j)\ge \frac{3r_j}{4}.$$
--   2. There are a binary multi-tape Turing machine $\mathsf{Gen}$ with finitely many states and a polynomial $p$ such that, on input $1^j0$, $\mathsf{Gen}$ outputs the two generator matrices within $p(r_j)$ steps. The matrices are written as `generatorBits`: the dimension in unary, then each basis row as $b$-bit field symbols.
--   3. There is a binary multi-tape machine $\mathsf{Enc}$ that, on input $1^j0$, a selector bit and a message $u$, outputs the codeword $\sum_i u_i\,\mathrm{basis}_i$ of $V_j$ (selector $0$) or of $W_j$ (selector $1$) within $p(r_j)$ steps.
--
--   This is the paper's assertion that Garcia–Stichtenoth compatible codes exist and that their generator matrices can be constructed and their codewords encoded deterministically in $\mathrm{poly}(r_j)$ time. The machine model is the one of Complexitylib/Cslib, whose closure library supports composition, pairing, folds and arithmetic. This statement implies the platform's Theorem 3.2: the proved bridge from multi-tape machines to finite TM2 programs turns $\mathsf{Gen}$ and $\mathsf{Enc}$ into the required `EffectivePairFamily`.
--
--   **Formalization Note.** The machines are `Turing.MultiTapeTM.ComputableInTimeAndSpace` certificates on `List Bool` with the identity encoding `encBits`. Their time bounds are arbitrary functions of the input, required to be at most $p(r_j)$ on the specified inputs.
-- source:
--   Wang–Wang–Wu, An Explicit and Optimal Separation of BPP from NP in NOF Communication Complexity, STOC 2027 submission #750, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/750.pdf, p.7 Theorem 3.2 (Garcia–Stichtenoth compatible codes, [GS96, SAK+01]) and Appendix A pp.11–13 (construction and polynomial-time generation/encoding)

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List

namespace NOFSeparation750.CodedGIP
theorem theorem_3_2_multitape (k a : ℕ) (hk : 2 ≤ k) (ha : Allowed k a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 4 ^ a) :
    ∃ D : PairFamily F a, ∃ codec : (Fin (2 * a) → Bool) ≃ F,
      (∀ j, Compatible (D j).small.code (D j).large.code k (6 / (2 ^ a : ℝ)) (3 / 4)) ∧
      ∃ (gen enc : List Bool → List Bool) (tg sg te se : List Bool → ℕ) (p : Polynomial ℕ),
        Turing.MultiTapeTM.ComputableInTimeAndSpace gen Turing.MultiTapeTM.encBits
          Turing.MultiTapeTM.encBits tg sg ∧
        Turing.MultiTapeTM.ComputableInTimeAndSpace enc Turing.MultiTapeTM.encBits
          Turing.MultiTapeTM.encBits te se ∧
        ∀ j,
          (gen (unary j) = generatorBits codec (D j).small ++ generatorBits codec (D j).large ∧
            tg (unary j) ≤ p.eval (codeLength a j)) ∧
          (∀ u : Fin (D j).small.dimension → F,
            enc (unary j ++ [false] ++ fieldVectorBits codec u) =
              fieldVectorBits codec ((D j).small.encode u).val ∧
            te (unary j ++ [false] ++ fieldVectorBits codec u) ≤ p.eval (codeLength a j)) ∧
          (∀ u : Fin (D j).large.dimension → F,
            enc (unary j ++ [true] ++ fieldVectorBits codec u) =
              fieldVectorBits codec ((D j).large.encode u).val ∧
            te (unary j ++ [true] ++ fieldVectorBits codec u) ≤ p.eval (codeLength a j)) := by sorry

end NOFSeparation750.CodedGIP
