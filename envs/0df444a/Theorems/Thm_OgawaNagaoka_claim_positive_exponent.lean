-- Prove2me | Theorems.Thm_OgawaNagaoka_claim_positive_exponent
-- name    : OgawaNagaoka.claim_positive_exponent
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:25:29.993652+00:00
-- url     : https://prove2.me/theorems/3450a4d5-cefc-4ef7-8162-635ca1b0882f
-- title:
--   Claim before Theorem 2: $R>C\Rightarrow-sR+\min_\pi E_0(s,\pi)>0$ for $s\in(t,0)$
-- statement:
--   Let $i\mapsto\rho_i$ be a classical-quantum channel and $C=\max_\pi I(\pi)$. If $R>C$, there exists $-1<t<0$ such that for every $s\in(t,0)$,
--
--   $$
--   -sR+\min_{\pi\in P_{\mathcal X}}E_0(s,\pi)>0 .
--   $$
--
--   Combined with Theorem 1 this gives an exponent $r>0$ with $\mathrm{Pe}\ge1-e^{-nr}$ for all codes of rate at least $R$.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - reading: $C$ (the operational capacity, p.2) → `holevoCap ρ` $=\max_\pi I(\pi)$; reason: the paper identifies $C$ with $\max_\pi I(\pi)$ by the quantum coding theorem, and the claim is derived from Lemma 3, which involves only $I(\pi)$
--   - encoding: $\max$ / $\min$ over the probability distributions $P_{\mathcal X}$ (or $P_{\mathcal X^n}$) → real `sSup` / `sInf` of the image of `stdSimplex`; reason: the simplex is nonempty and compact for a nonempty alphabet and the function is continuous, so the supremum (infimum) is the attained maximum (minimum); with an empty alphabet the bound is vacuous or trivially true
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, claim before Theorem 2, p.9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_OgawaNagaoka_holevoCap
import Definitions.Def_OgawaNagaoka_E0

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, claim before Theorem 2, p.9: if `R > C` there exists `−1 < t < 0` such
that for all `s ∈ (t, 0)`, `−sR + min_π E₀(s, π) > 0`.

**Formalization Note.** `C` is `holevoCap ρ = max_π I(π)` (see `holevoCap`). The minimum over `π`
is the real `sInf` of the image of the simplex under `E₀(s, ·)`. -/
theorem claim_positive_exponent {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) (R : ℝ) (hR : holevoCap ρ < R) :
    ∃ t ∈ Set.Ioo (-1 : ℝ) 0, ∀ s ∈ Set.Ioo t 0,
      0 < -s * R + sInf (E0 ρ s '' stdSimplex ℝ A) := by sorry

end OgawaNagaoka
