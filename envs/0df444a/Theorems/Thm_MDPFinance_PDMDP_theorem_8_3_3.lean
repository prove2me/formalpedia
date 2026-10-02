-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_3_3
-- name    : MDPFinance.PDMDP.theorem_8_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:13.650228+00:00
-- url     : https://prove2.me/theorems/38c4c19e-62be-445f-a8ab-aeb1d8902e3a
-- title:
--   Theorem 8.3.3 — existence of an optimal policy, finite-horizon chain
-- statement:
--   The finite-horizon analogue of Theorem 8.3.1 (proved, per the book, "similar to the proof of Theorem 8.2.7 a)"): under an upper bounding function for the finite-horizon chain and the continuity/compactness assumptions of Theorem 8.3.1, a decision rule $f^*(t,x)$ achieving the pointwise maximum of $u \mapsto r(x,u)+\sum_yq_{xy}(u)V(t,y)$ exists, yielding an optimal Markov policy $\pi^*_t = f^*(t,X_{t-})$; moreover $V$ is a genuine fixed point of the operator $T$, stated with its full explicit right-hand side $V(t,x)=e^{-\lambda(T-t)}g(x)+\int_0^{T-t}e^{-\lambda s}\sup_u[r(x,u)+\lambda\sum_yV(t+s,y)Q(\{y\}\mid x,u)]\,ds$, per this chunk's convention (also used for `theorem_8_2_8`) of never weakening a fixed-point conclusion to bare qualitative existence.
--
--   **Formalization Note.** The decision rule $f^*: E' \to U$ is converted to a genuine Markov policy $(f_n) : \mathbb N \to \mathbb R \to E \to A$ by holding the jump-time argument fixed at each stage and letting the elapsed-time argument inside each control function vary: $(f_n(t,x))(s) := f^*(t+s,x)$, matching $\pi_t = f_n(T_n,Z_n)(t-T_n)$'s own shape (Eq. before Theorem 8.3.2).
--
--   **Moderation note.** The draft's finite-horizon chain theorem had no measurability for the maximizer, an unconstrained policy in place of the book's `π^*_t = f^*(t + T_n, Z_n)`, and a real fixed-point equation. Now: there is a jointly measurable `f^*(t,x)` attaining the supremum on `[0,T]`, the policy defined by `α_n(s) = f^*(t + s, x)` attains `V_∞` on `[0,T]`, and `V_∞` satisfies the fixed-point equation on `[0,T]` in `[-∞,∞]`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 261, PDF 272, Theorem 8.3.3

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Chain

open MeasureTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [TopologicalSpace.MetrizableSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.3.3 (Bäuerle–Rieder, p. 261, PDF 272). Suppose the finite-horizon continuous-time
Markov Decision Chain has an upper bounding function `b` and the continuity and compactness
assumptions (i)-(iv) of Theorem 8.3.1 hold. Then there exists an optimal Markov policy `π^*_t =
f^*(t,X_{t-})`, `t ∈ [0,T]`, for a measurable decision rule `f^* : E' → U`, `f^*(t,x)` a maximum
point of `u ↦ r(x,u) + Σ_y q_{xy}(u) V(t,y)`; the policy `(f_n)` with `f_n(t,x)(s) := f^*(t+s,x)`
attains `V` on `E' = [0,T] × E`. Moreover `V` is a fixed point of `T` in `IB_b^+`: `V(t,x) =
e^{-λ(T-t)} g(x) + ∫_0^{T-t} e^{-λs} sup_{u∈U} [r(x,u) + λ Σ_y V(t+s,y) Q({y}|x,u)] ds`. -/
theorem theorem_8_3_3 (Ch : MDChainFinite E U) (b : E → ℝ) (cr cg cQ : ℝ)
    (hbound : IsUpperBoundingFunctionChainFinite Ch b cr cg cQ)
    (hUcompact : IsCompact (Set.univ : Set U))
    (hqcont : ∀ x y, Continuous (Ch.q x y))
    (hbsum_cont : ∀ x, Continuous fun u => (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)).toReal)
    (hrusc : ∀ x, UpperSemicontinuous fun u => Ch.r (x, u)) :
    (∃ fstar : ℝ → E → U, Measurable (fun p : ℝ × E => fstar p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x,
          ((Ch.r (x, fstar t x) : ℝ) : EReal) +
              (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x (fstar t x)) (Ch.Vinf t) -
                Ch.Vinf t x) =
            ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
              (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) (Ch.Vinf t) - Ch.Vinf t x))) ∧
        ∃ f : ℕ → ℝ → E → ControlFn U, IsChainPolicyFinite f ∧
          (∀ n t x s, (f n t x).1 s = fstar (t + s) x) ∧
          ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x, Ch.Jinf f t x = Ch.Vinf t x) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x, Ch.Vinf t x = Ch.T Ch.Vinf t x := by sorry

end MDPFinance.PDMDP
