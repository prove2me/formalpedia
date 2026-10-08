-- Prove2me | Theorems.Thm_KedlayaUmans_FrobeniusLift_eq_6_2
-- name    : KedlayaUmans.FrobeniusLift.eq_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:35.156785+00:00
-- url     : https://prove2.me/theorems/0de1ed59-05bd-4a8c-8ca1-bd32a3423f43
-- title:
--   Eq. (6.2) — deg g_α^{(i)} = deg g_α and g_α^{(i)}(1) = α_i
-- statement:
--   Let $p$ be a prime, $\mathbb F_q$ a finite field of characteristic $p$, $P \in \mathbb F_p[W]$ irreducible over $\mathbb F_p$ of degree $c$, $h = p^c$, $K = \mathbb F_p[W]/(P(W)) \subseteq R = \mathbb F_q[W]/(P(W))$, $\eta$ a primitive element of $K$, and $E(Z) = Z^{h-1} - \eta$. Let $m, d$ be natural numbers with $d \ge 1$ and $h > m^2 d$. For $\alpha \in \mathbb F_q^m$ let $g_\alpha \in R[Z]$ be the interpolant of Eq. (6.1), and for $i \ge 0$ let
--   $$g_\alpha^{(i)}(Z) = (g_\alpha(Z))^{h^i} \bmod E(Z),$$
--   the remainder on division by the monic polynomial $E$. Then for every $i = 0, 1, \dots, m-1$:
--
--   1. $\deg g_\alpha^{(i)} = \deg g_\alpha$;
--   2. $$g_\alpha^{(i)}(1) = \alpha_i. \tag{6.2}$$
--
--   Here $\alpha_i \in \mathbb F_q$ is viewed in $R$. The degree statement is what later keeps $f(g_\alpha^{(0)}, \dots, g_\alpha^{(m-1)})$ below the degree of $E$.
--
--   **Formalization Note** Degrees are `natDegree` (so the zero polynomial has degree $0$).
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 19, proof of Lemma 6.1, Eq. (6.2) and the sentence before it

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

open Polynomial

namespace KedlayaUmans.FrobeniusLift

/-- §6, p. 19, (6.2) and the degree claim before it: for `i = 0, …, m-1`, the polynomial
`g_α^{(i)} = g_α^{h^i} mod E` has the same degree as `g_α`, and `g_α^{(i)}(1) = α_i`. -/
theorem eq_6_2 (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (α : Fin m → F) (i : Fin m) :
    (gIter p F P η α i).natDegree = (gAlpha p F P η α).natDegree ∧
      (gIter p F P η α i).eval 1 = algebraMap F (R p F P) (α i) := by sorry

end KedlayaUmans.FrobeniusLift
