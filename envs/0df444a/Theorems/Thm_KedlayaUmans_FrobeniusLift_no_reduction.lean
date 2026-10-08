-- Prove2me | Theorems.Thm_KedlayaUmans_FrobeniusLift_no_reduction
-- name    : KedlayaUmans.FrobeniusLift.no_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:35.672306+00:00
-- url     : https://prove2.me/theorems/43a8cdfd-cead-4dc9-a3ec-50db44fd9910
-- title:
--   §6, pp. 19–20 — f*(φ(α)) is represented by f(g_α^{(0)}, …, g_α^{(m−1)}), with no reduction mod E needed
-- statement:
--   Let $p$ be a prime, $\mathbb F_q$ a finite field of characteristic $p$, $P \in \mathbb F_p[W]$ irreducible over $\mathbb F_p$ of degree $c$, $h = p^c$, $R = \mathbb F_q[W]/(P(W))$, $\eta$ a primitive element of $\mathbb F_p[W]/(P(W))$, $E(Z) = Z^{h-1} - \eta$ and $S = R[Z]/(E(Z))$. Let $m, d$ be natural numbers with $d \ge 1$ and $h > m^2 d$, and let $f \in \mathbb F_q[X_0, \dots, X_{m-1}]$ have degree at most $d-1$ in each variable. For $\alpha \in \mathbb F_q^m$ let $\varphi(\alpha) \in S$ be the lift, $g_\alpha^{(i)} = g_\alpha^{h^i} \bmod E$, and $f^*(Y) = f(Y, Y^h, \dots, Y^{h^{m-1}}) \in S[Y]$. Then
--
--   1. the canonical representative (remainder modulo $E$) of $f^*(\varphi(\alpha)) \in S$ is
--   $$f\big(g_\alpha^{(0)}(Z), g_\alpha^{(1)}(Z), \dots, g_\alpha^{(m-1)}(Z)\big) \bmod E(Z);$$
--   2. no reduction takes place:
--   $$f\big(g_\alpha^{(0)}, \dots, g_\alpha^{(m-1)}\big) \bmod E = f\big(g_\alpha^{(0)}, \dots, g_\alpha^{(m-1)}\big).$$
--
--   The point is that $E$ has degree $h - 1 \ge m^2 d$, which exceeds the degree of $f(g_\alpha^{(0)}, \dots, g_\alpha^{(m-1)})$.
--
--   **Formalization Note** The coefficients of $f$ are viewed in $R$ through $\mathbb F_q \subseteq R$; the substituted polynomial is `MvPolynomial.eval₂` with the $g_\alpha^{(i)}$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), pp. 19-20, proof of Lemma 6.1 (unnumbered)

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

open Polynomial

namespace KedlayaUmans.FrobeniusLift

/-- §6, pp. 19–20, in the proof of Lemma 6.1: the canonical representative of `f*(φ(α))` is
`f(g_α^{(0)}, …, g_α^{(m-1)}) mod E`, and since `deg E = h - 1 > (d-1)m(m-1)` no reduction takes place:
`f(g_α^{(0)}, …, g_α^{(m-1)}) mod E = f(g_α^{(0)}, …, g_α^{(m-1)})`. -/
theorem no_reduction (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1))
    (f : MvPolynomial (Fin m) F) (hf : ∀ i, f.degreeOf i ≤ d - 1) (α : Fin m → F) :
    AdjoinRoot.modByMonicHom (E_monic p F P η) ((fStar p F P η f).eval (phi p F P η α)) =
        MvPolynomial.eval₂ (C.comp (algebraMap F (R p F P))) (fun i : Fin m => gIter p F P η α i) f
          %ₘ E p F P η ∧
      MvPolynomial.eval₂ (C.comp (algebraMap F (R p F P))) (fun i : Fin m => gIter p F P η α i) f
          %ₘ E p F P η =
        MvPolynomial.eval₂ (C.comp (algebraMap F (R p F P))) (fun i : Fin m => gIter p F P η α i) f := by sorry

end KedlayaUmans.FrobeniusLift
