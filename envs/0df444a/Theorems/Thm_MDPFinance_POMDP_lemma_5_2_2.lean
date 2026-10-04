-- Prove2me | Theorems.Thm_MDPFinance_POMDP_lemma_5_2_2
-- name    : MDPFinance.POMDP.lemma_5_2_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:14:01.357126+00:00
-- url     : https://prove2.me/theorems/8f620181-a145-4f94-8847-6c7455dce327
-- title:
--   Lemma 5.2.2 — the filter-recursion identity
-- statement:
--   For measurable $v$ and $a_n\in D(x_n)$, provided the integrals exist,
--   $$\iint \mu_n(dy_n\mid h_n)\,Q(d(x_{n+1},y_{n+1})\mid x_n,y_n,a_n)\,v(h_n,x_{n+1},y_{n+1})
--   = \iint \mu_n(dy_n\mid h_n)\,Q^X(dx_{n+1}\mid x_n,y_n,a_n)\,\Phi(x_n,\mu_n,a_n,x_{n+1})
--   (dy_{n+1})\,v(h_n,x_{n+1},y_{n+1}).$$
--
--   This is the technical engine of the whole filtering theory: it says integrating against the true
--   joint transition $Q$, started from the current posterior $\mu_n$, agrees with integrating
--   against the *marginal* $Q^X$ composed with the *updated* posterior $\Phi(\cdot)$ — exactly
--   what makes $\mu_n$'s own recursive definition (Eq. (5.4)) the right one, and what drives the
--   induction proving Theorem 5.2.1.
--
--   **Formalization Note.** "Provided the integrals exist" is carried as two explicit `Integrable`
--   hypotheses (one per side), not silently dropped — this chunk's own flagged pitfall.
--
--   **Moderation note.** "Provided the integrals exist" now covers every integral on both sides, inner and outer (`hv_int0`, `hv_int2a`, `hv_int2b` in addition to the two outer hypotheses); with only the outer hypotheses an inner Bochner integral that does not exist is a default $0$ and the identity can fail.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 152, PDF 165, Lemma 5.2.2

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_FilterData

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

/-- Lemma 5.2.2 (Bäuerle–Rieder, p. 152, PDF 165). Let `v` be measurable. Then for the observable
history `(xs,as)` at time `n` and `a_n ∈ D(x_n)`, provided the integrals exist:
`∫∫ μ_n(dy_n|xs,as) Q(d(x_{n+1},y_{n+1})|x_n,y_n,a_n) v(xs,as,x_{n+1},y_{n+1}) =
∫∫ μ_n(dy_n|xs,as) Q^X(dx_{n+1}|x_n,y_n,a_n) Φ(x_n,μ_n,a_n,x_{n+1})(dy_{n+1})
v(xs,as,x_{n+1},y_{n+1})`, where `Q^X(·|x,y,a) := Q(·×E_Y|x,y,a)` is realized as the pushforward
`(Q(·|x,y,a)).map Prod.fst`. "Provided the integrals exist" is carried for every integral on
both sides (inner and outer), so that no Bochner integral is a default `0`. -/
theorem lemma_5_2_2 {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M) (n : ℕ)
    (xs : ℕ → EX) (as : ℕ → A) (han : as n ∈ M.Dx (xs n))
    (v : (ℕ → EX) → (ℕ → A) → EX → EY → ℝ)
    (hv_meas : Measurable fun p : (ℕ → EX) × (ℕ → A) × EX × EY => v p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hv_int0 : ∀ yn, Integrable (fun p : EX × EY => v xs as p.1 p.2) (M.Q ((xs n, yn), as n)))
    (hv_int1 : Integrable
      (fun yn => ∫ p : EX × EY, v xs as p.1 p.2 ∂(M.Q ((xs n, yn), as n)))
      (Fd.mu M n xs as).toMeasure)
    (hv_int2a : ∀ x', Integrable (fun y' => v xs as x' y')
      (Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure)
    (hv_int2b : ∀ yn, Integrable
      (fun x' : EX => ∫ y', v xs as x' y' ∂(Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure)
      ((M.Q ((xs n, yn), as n)).map Prod.fst))
    (hv_int2 : Integrable
      (fun yn => ∫ x' : EX, ∫ y', v xs as x' y'
          ∂(Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure
        ∂(M.Q ((xs n, yn), as n)).map Prod.fst)
      (Fd.mu M n xs as).toMeasure) :
    ∫ yn, (∫ p : EX × EY, v xs as p.1 p.2 ∂(M.Q ((xs n, yn), as n))) ∂(Fd.mu M n xs as).toMeasure =
      ∫ yn, (∫ x' : EX, ∫ y', v xs as x' y'
          ∂(Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure
        ∂(M.Q ((xs n, yn), as n)).map Prod.fst) ∂(Fd.mu M n xs as).toMeasure := by sorry

end MDPFinance.POMDP
