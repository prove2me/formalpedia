-- Prove2me | Theorems.Thm_NashOrTriangle_Supplement_theorem_B_1
-- name    : NashOrTriangle.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:51:18.922656+00:00
-- url     : https://prove2.me/theorems/a849fcf1-6e03-4978-b6a9-fff7ad416c72
-- title:
--   Theorem B.1 — for Turing-machine games, having a $t$-triangle is $\Sigma^0_1$-complete; triangles can be found but their size is not recursively bounded
-- statement:
--   **Theorem B.1.** Fix $t\ge2$ and consider binary games on $\mathbb N\times\mathbb N$ given by a total utility Turing machine and exact best-response Turing machines, all running in polynomial time on unary strategy descriptions.
--
--   1. (a) Deciding whether the game has a $t$-triangle is $\Sigma^0_1$-complete: it is $\Sigma^0_1$ on valid instances, and every $\Sigma^0_1$ set reduces to it by a computable map producing valid instances.
--   2. (b) Under the promise that a $t$-triangle exists, one can be found using the utility Turing machine alone: one program, given only the utility machine of any valid instance having a $t$-triangle, outputs a $t$-triangle of it.
--   3. (b) No recursive function of the description length and $t$ bounds the length of the output: for every computable $g$ there is a valid instance $I$ with a $t$-triangle all of whose $t$-triangles, written in unary, have length greater than $g(|I|,t)$.
--   4. (b) No recursive function bounds the running time: for every computable $g$ and every Turing machine that receives the instance, there is a valid instance with a $t$-triangle on which the machine does not output a $t$-triangle within $g(|I|,t)$ steps.
--
--   The theorem is the recursion-theoretic counterpart of the information-theoretic impossibility of finding triangles in the oracle model.
--
--   **Formalization Note** Programs are Mathlib partial recursive codes and polynomial time is Mathlib's `TM2ComputableInPolyTime`; the description length $|I|$ is the binary length of the instance code. The running-time clause uses Mathlib's multi-stack Turing machines with the instance code written in binary on the input stack and the triangle written on the output stack.
--
--   Differences from the source:
--   - encoding: utility and BR Turing machines, polynomial time, strategy descriptions in unary, description length → an instance code I decoding to three Nat.Partrec.Code programs; ValidExactPoly (total binary utility, exact BR programs, each computing a TM2ComputableInPolyTime function with unary strategies); description length Nat.size I; reason: Mathlib's models of computability and polynomial time; any two such encodings are recursively related
--   - encoding: Σ⁰₁-complete → PromiseSigma01Complete: membership on valid instances by a total computable relation, and a computable reduction to valid instances from every Σ⁰₁ set; reason: completeness of a promise problem; reductions from the halting problem give every Σ⁰₁ set
--   - reading: one can be found using the utility Turing machine alone → one partial recursive program that maps the code of the utility program of every valid instance with a t-triangle to the code of a t-triangle of it; reason: t is fixed before the program, as in 'for any t ≥ 2'
--   - reading: no recursive function of the description length and t bounds the length of the output → for every computable g there is a valid instance with a t-triangle all of whose t-triangles have unary length triLength > g(Nat.size I, t); reason: strategies are written in unary, so the output length is the unary length of the triangle
--   - reading: or the running time → for every computable g and every FinTM2 finder (input: the instance code in binary, output: encTri over {0,1,#}) there is a valid instance with a t-triangle on which the finder outputs no t-triangle within g(Nat.size I, t) steps; reason: running time in a step-counted Turing-machine model; the finder may read the whole instance
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem B.1, p.22 (PDF p.23); model: Appendix B, first paragraph, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_NashOrTriangle_IsTriangle
import Definitions.Def_NashOrTriangle_HasTriangle
import Definitions.Def_NashOrTriangle_Supplement_TMGame
import Definitions.Def_NashOrTriangle_Supplement_Arithmetical

namespace NashOrTriangle.Supplement

open Nat.Partrec Computability

/-- **Theorem B.1** (triangles in the Turing-machine model). For any `t ≥ 2`,
(a) Deciding whether the game has a `t`-triangle is `Σ⁰₁`-complete.
(b) Under the promise that a `t`-triangle exists, one can be found using the utility Turing
machine alone, but no recursive function of the description length and `t` bounds the length of
the output, or the running time.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem B.1, printed p. 22 (PDF p. 23);
the model is the first paragraph of Appendix B, same page.

**Formalization Note** Instances are codes `I` of a triple of programs (`tmInstance`); the
promise `ValidExactPoly` is a total binary utility program and exact BR programs, all computing
polynomial-time functions on unary strategies. The four conjuncts are:
1. (a) `Σ⁰₁`-completeness of "has a `t`-triangle" as a promise problem (`PromiseSigma01Complete`).
2. (b, finding) one program `F` that, given only the code of the utility program of any valid
   instance with a `t`-triangle, halts with the `Encodable` code of the pair of lists
   (rows, columns) of a `t`-triangle.
3. (b, output length) for every computable `g`, some valid instance has a `t`-triangle and every
   `t`-triangle of it has unary length `triLength` greater than `g(Nat.size I, t)`.
4. (b, running time) for every computable `g` and every Turing machine `F` (Mathlib `FinTM2`, input
   the binary code of the whole instance, output over `{0, 1, #}`), some valid instance has a
   `t`-triangle on which `F` does not output (`encTri`) any `t`-triangle within `g(Nat.size I, t)`
   steps. -/
theorem theorem_B_1 (t : ℕ) (ht : 2 ≤ t) :
    PromiseSigma01Complete ValidExactPoly (fun I => HasTriangle (tmPayoff I) t) ∧
    (∃ F : Code, ∀ I : ℕ, ValidExactPoly I → HasTriangle (tmPayoff I) t →
      ∃ a b : Fin t → ℕ, IsTriangle (tmPayoff I) a b ∧
        Encodable.encode (List.ofFn a, List.ofFn b) ∈ F.eval (Encodable.encode (tmInstance I).1)) ∧
    (∀ g : ℕ → ℕ → ℕ, Computable₂ g → ∃ I : ℕ, ValidExactPoly I ∧ HasTriangle (tmPayoff I) t ∧
      ∀ a b : Fin t → ℕ, IsTriangle (tmPayoff I) a b → g (Nat.size I) t < triLength a b) ∧
    (∀ g : ℕ → ℕ → ℕ, Computable₂ g → ∀ F : Turing.TM2ComputableAux Bool (Fin 3),
      ∃ I : ℕ, ValidExactPoly I ∧ HasTriangle (tmPayoff I) t ∧
        ¬ ∃ a b : Fin t → ℕ, IsTriangle (tmPayoff I) a b ∧
          Nonempty (Turing.TM2OutputsInTime F.tm ((encodeNat I).map F.inputAlphabet.symm)
            (some ((encTri a b).map F.outputAlphabet.symm)) (g (Nat.size I) t))) := by sorry

end NashOrTriangle.Supplement
