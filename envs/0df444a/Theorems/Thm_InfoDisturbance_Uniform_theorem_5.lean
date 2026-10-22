-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_theorem_5
-- name    : InfoDisturbance.Uniform.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:39.38774+00:00
-- url     : https://prove2.me/theorems/d258951e-7591-44fc-984a-df268f62fc07
-- title:
--   Theorem 5, p. 9 — on the uniform ensemble the square-root dynamics disturbs no more than any finite instrument for the same POVM
-- statement:
--   Let $\{F_b\}_{b\in B}$ be a POVM on $\mathbb C^d$, $d\ge1$, with finitely many outcomes, and let $\{A_{bi}\}$ be any finite instrument compatible with it, $\sum_iA_{bi}^\dagger A_{bi}=F_b$ for every $b$, with overall operation $\mathcal A(\rho)=\sum_{b,i}A_{bi}\rho A_{bi}^\dagger$. Let $\mathcal S(\rho)=\sum_bF_b^{1/2}\rho F_b^{1/2}$ be the square-root operation and $D$ the average disturbance on the uniform ensemble $\Omega$ (Eq. (9)). Then
--   $$D(\mathcal S)\;\le\;D(\mathcal A),$$
--   that is, one-term conditional dynamics, $A_b=F_b^{1/2}$, give a minimally disturbing way of measuring any given POVM on the uniform ensemble.
--
--   This is the paper's main result: it lets one compute, for every measurement, the minimal disturbance compatible with it on the uniform ensemble (Eqs. (34)–(35)). The instrument may have several HK operators per outcome; for one operator per outcome the statement is part of Theorem 8.
--
--   **Formalization Note** $D(\mathcal E)=1-$`averageFidelity d hd E`. Every outcome uses the same finite Kraus index type $I$, shorter lists being padded with zero operators; finiteness is the paper's "any (finite)" (p. 10). $0<d$ is required by the published Haar measure.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 9, Theorem 5; proof pp. 9–10

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem theorem_5 (d : ℕ) (hd : 0 < d) {B I : Type*} [Fintype B] [Fintype I]
    (F : B → Matrix (Fin d) (Fin d) ℂ) (hF : IsPOVM F)
    (A : B → I → Matrix (Fin d) (Fin d) ℂ) (hA : IsCompatible F A) :
    disturbance d hd (sqrtOperation F) ≤ disturbance d hd (instrumentOperation A) := by sorry

end InfoDisturbance.Uniform
