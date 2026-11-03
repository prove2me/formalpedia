-- Prove2me | Theorems.Thm_FreeOrderEPTAS_claim_2_4
-- name    : FreeOrderEPTAS.claim_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:21.770816+00:00
-- url     : https://prove2.me/theorems/21b4d7b0-7f58-4da5-a351-dbd449215924
-- title:
--   Claim 2.4 — concentration of the small jobs
-- statement:
--   Let $\epsilon\in(0,1)$, $\xi=\epsilon/2$, $\delta\in(0,1)$ with (9), $y$ feasible for (LP), and a rounding with (P1)–(P3). For $d\in A_i$ with $\mathcal T^{(t)}_{id}=0$, if $S^\downarrow_{idt}$ is an integer multiple of $\epsilon/T$ then
--   $$\mathbb P\big((\mathsf A)_{idt}\ge(1-\epsilon)S^\downarrow_{idt}\big)\ge1-\frac1{2mDT},\qquad(\mathsf A)_{idt}=\sum_{j\in J_t}\ell_{ijd}Y_{(i,t),j}.$$
--
--   This is where $\delta$ is used: small jobs have load at most $\delta$, so (P3) applies to $\ell_{ijd}/\delta$.
--
--   Differences from the source:
--   - generalization: $S^\downarrow_{idt}=\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$ and the $\delta$ of p.12 → any integer multiple of $\epsilon/T$, and any $\delta\in(0,1)$ with (9); reason: the proof uses exactly these two facts, and covers the capped guess
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Claim 2.4, p.14; proof, pp.15–16

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace FreeOrderEPTAS

/-- Claim 2.4, p.14 (arXiv:2007.13121v3): `P((A)_idt ≥ (1 - ϵ) S↓_idt) ≥ 1 - 1/(2mDT)`, for a small
triple, `y` feasible for (LP), `ξ = ϵ/2`, `δ` with (9), and `S↓_idt` a multiple of `ϵ/T`. -/
theorem claim_2_4 {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h9 : δ ≤ ϵ ^ 3 / (16 * (numTypes I ϵ δ : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ))))
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (y : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Feasible y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd)
    (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)) (hd : d ∈ I.A i)
    (hsmall : typeOf I ϵ δ t i d = 0)
    (hS : ∃ k : ℕ, Slo i d t = (k : ℝ) * (ϵ / (numTypes I ϵ δ : ℝ))) :
    1 - 1 / (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ)) ≤
      pr (rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y)
        {Y | (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)} := by sorry

end FreeOrderEPTAS
