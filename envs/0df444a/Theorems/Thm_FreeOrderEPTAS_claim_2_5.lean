-- Prove2me | Theorems.Thm_FreeOrderEPTAS_claim_2_5
-- name    : FreeOrderEPTAS.claim_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:24.746243+00:00
-- url     : https://prove2.me/theorems/51b8f342-0a14-49b8-9613-dc656d22896b
-- title:
--   Claim 2.5 — large jobs (corrected: capped small-load guess)
-- statement:
--   Let $\epsilon,\delta\in(0,1)$, the guesses induced by $x^{(\mathrm{IP})}$, $y$ meeting (S1)–(S3), and a rounding with (P2). For $d\in A_i$ with $\mathcal T^{(t)}_{id}\ge1$, every $Y$ in the support satisfies
--   $$(\mathsf B)_{idt}=\sum_{j\in J_t}\ell_{ijd}Y_{(i,t),j}\ge(1-\epsilon)\min\Big\{\sum_{j\in J_t}\ell_{ijd}x^{(\mathrm{IP})}_{ij},1\Big\}.$$
--
--   It uses $N^\downarrow_{it}\ge\min\{N^{(\mathrm{IP})}_{it},1/\delta\}$ and the geometric segments of the type.
--
--   Differences from the source:
--   - correction: $S^\downarrow_{idt}=\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$, p.10 → $S^\downarrow_{idt}=\lfloor\min\{S^{(\mathrm{IP})}_{idt},1\}\rfloor_{\epsilon/T}$; reason: the printed guess has order $n$ values ($n$ jobs of load $\delta$ in one class, all on machine $i$), a PTAS count against the stated $O((T/\epsilon)^{O(mDT)})$; every step of the proof survives the cap
--   - generalization: $y^*$, feasible for (LP), for $x^{(\mathrm{IP})}$ feasible and $\xi=\epsilon/2$ → any $y$ meeting (S1)–(S3), any binary $x^{(\mathrm{IP})}$, any $\xi$; reason: the proof uses (P2) and $N^\downarrow\ge\min\{N^{(\mathrm{IP})},1/\delta\}$ only; the source’s case is covered
--   - encoding: "with probability 1" → for every point of the support of the law; reason: the laws are on a finite set
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Claim 2.5, p.14; proof, p.16

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace FreeOrderEPTAS

/-- Claim 2.5, p.14 (arXiv:2007.13121v3): with probability 1,
`(B)_idt ≥ (1 - ϵ) min{∑_{j ∈ J_t} ℓ_ijd x^(IP)_ij, 1}` on a class with `T^(t)_id ≥ 1`. -/
theorem claim_2_5 {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (x : Assignment m n)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ ξ Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ ξ Nlo Nhi Slo).MeetsS123 y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd)
    (Y : Assignment m n) (hY : Y ∈ (rnd (mkLP I ϵ δ ξ Nlo Nhi Slo) y).support)
    (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)) (hd : d ∈ I.A i)
    (hlarge : 1 ≤ typeOf I ϵ δ t i d) :
    (1 - ϵ) * min (Sip I ϵ δ x i d t) 1 ≤
      ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j) := by sorry

end FreeOrderEPTAS
