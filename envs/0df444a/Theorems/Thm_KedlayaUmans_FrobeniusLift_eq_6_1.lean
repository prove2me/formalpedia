-- Prove2me | Theorems.Thm_KedlayaUmans_FrobeniusLift_eq_6_1
-- name    : KedlayaUmans.FrobeniusLift.eq_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:23.857494+00:00
-- url     : https://prove2.me/theorems/ff65e348-6fa3-438b-adb9-2bf2bdbb6d5b
-- title:
--   Eq. (6.1) — g_α has degree ≤ m − 1 and g_α(ηⁱ) = σ^{−i}(α_i); σ^{−i} on 𝔽_q gives preimages under σ^i
-- statement:
--   Let $p$ be a prime, $\mathbb F_q$ a finite field of characteristic $p$, $P \in \mathbb F_p[W]$ irreducible over $\mathbb F_p$ of degree $c$, $h = p^c$, $K = \mathbb F_p[W]/(P(W)) \subseteq R = \mathbb F_q[W]/(P(W))$, and $\eta$ a primitive element of $K$ (multiplicative order $h-1$). Let $m, d$ be natural numbers with $d \ge 1$ and $h > m^2 d$. Let $\sigma^i : R \to R$ be $x \mapsto x^{h^i}$, let $\sigma^{-i} : \mathbb F_q \to \mathbb F_q$ be the inverse of the automorphism $x \mapsto x^{h^i}$ of $\mathbb F_q$, and let $g_\alpha \in R[Z]$ be the Lagrange interpolant defined in the companion definition file. Then:
--
--   1. $g_\alpha$ is well defined in the sense of the paper: for every $i \ge 0$ and every $a \in \mathbb F_q$, $\sigma^{-i}(a) \in \mathbb F_q \subseteq R$ is a preimage of $a$ under the endomorphism $\sigma^i$ of $R$, i.e. $\sigma^i(\sigma^{-i}(a)) = a$;
--   2. $\deg g_\alpha \le m - 1$;
--   3. for every $\alpha \in \mathbb F_q^m$ and every $i = 0, 1, \dots, m-1$,
--   $$g_\alpha(\eta^i) = \sigma^{-i}(\alpha_i). \tag{6.1}$$
--
--   Together these say that the explicit interpolant is the polynomial the paper uses to define the lift $\varphi(\alpha)$.
--
--   **Formalization Note** Degrees are `natDegree`, so for $m = 0$ (where $g_\alpha = 0$) item 2 reads $0 \le 0$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 19, Eq. (6.1) and the remark following it

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

open Polynomial

namespace KedlayaUmans.FrobeniusLift

/-- §6, p. 19, (6.1) and the remark that `g_α` is well defined: `σ^{-i}(a)` is a preimage of `a ∈ 𝔽_q`
under `σ^i` in `R`; `g_α` has degree at most `m - 1`; and `g_α(η^i) = σ^{-i}(α_i)` for `i = 0, …, m-1`. -/
theorem eq_6_1 (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (α : Fin m → F) :
    (∀ (i : ℕ) (a : F),
        sigma p F P i (algebraMap F (R p F P) (sigmaInv p F P i a)) = algebraMap F (R p F P) a) ∧
      (gAlpha p F P η α).natDegree ≤ m - 1 ∧
      ∀ i : Fin m, (gAlpha p F P η α).eval (ι p F P η ^ (i : ℕ)) =
        algebraMap F (R p F P) (sigmaInv p F P i (α i)) := by sorry

end KedlayaUmans.FrobeniusLift
