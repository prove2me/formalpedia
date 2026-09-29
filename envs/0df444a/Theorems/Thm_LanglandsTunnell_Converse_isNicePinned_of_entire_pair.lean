-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_isNicePinned_of_entire_pair
-- name    : LanglandsTunnell.Converse.isNicePinned_of_entire_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ec978af4-ae78-5a81-9b17-3a5907d8454e
-- title:
--   Pinned niceness from an entire pair satisfying a functional equation
-- statement:
--   Let $D$ be an $L$-datum indexed by a type $\iota$, so $D$ consists of norms $N_i\in\mathbb{N}$, Euler and dual polynomials $\mathrm{euler}_i,\mathrm{dual}_i\in\mathbb{C}[X]$, four multisets of archimedean shifts, a real abscissa, a real centre $c$ and a degree; let $\Lambda_S,\Lambda_S^{\vee}:\mathbb{C}\to\mathbb{C}$, let $\varepsilon\in\mathbb{C}$ and let $N\in\mathbb{R}$. Assume: $D$ is well formed (all $N_i\ge 2$; each $\mathrm{euler}_i$ and $\mathrm{dual}_i$ has constant term $1$ and degree at most $D.\mathrm{degree}$; every shift $\mu$ in the four multisets satisfies $-\operatorname{Re}\mu\le D.\mathrm{abscissa}$); $D$ converges, i.e. for $\operatorname{Re} s>D.\mathrm{abscissa}$ the families $\|\mathrm{euler}_i(N_i^{-s})-1\|$ and $\|\mathrm{dual}_i(N_i^{-s})-1\|$ are summable and both Euler products $L(D,s)$, $L^{\vee}(D,s)$ are non-zero; $0<N$; and $\Lambda_S(s)\neq 0$ for some $s$ with $\operatorname{Re} s>D.\mathrm{abscissa}$. Assume further given $\Lambda_0,\Lambda_0^{\vee}:\mathbb{C}\to\mathbb{C}$ with $\Lambda_0$ entire and bounded on every vertical strip, $\Lambda_0(s)=\Lambda_0^{\vee}(2c-s)$ for all $s$, and, for $\operatorname{Re} s>D.\mathrm{abscissa}$, $\Lambda_0(s)=\Lambda_S(s)\,\gamma(D,s)\,L(D,s)$ and $\Lambda_0^{\vee}(s)=\varepsilon N^{\,s-c}\Lambda_S^{\vee}(s)\,\gamma^{\vee}(D,s)\,L^{\vee}(D,s)$. Then `IsNicePinned D ΛS ΛSd ε N` holds: $D$ is well formed and convergent, $N>0$, and there exist entire functions $\Lambda,\Lambda^{\vee}$, each bounded on every vertical strip, with $\Lambda(s)=\Lambda_S(s)\gamma(D,s)L(D,s)$ and $\Lambda^{\vee}(s)=\Lambda_S^{\vee}(s)\gamma^{\vee}(D,s)L^{\vee}(D,s)$ for $\operatorname{Re} s>D.\mathrm{abscissa}$, and $\Lambda(s)=\varepsilon N^{\,c-s}\Lambda^{\vee}(2c-s)$ for all $s\in\mathbb{C}$.
--
--   This is the packaging step of the converse-theorem input: it converts a concretely constructed pair of entire completed integrals, related by the reflection $s\mapsto 2c-s$ and having the prescribed Euler-product expansions in the right half-plane, into the normalised form of analytic niceness with pinned $S$-parts $\Lambda_S,\Lambda_S^{\vee}$, root number $\varepsilon$ and conductor $N$. It is used by the constructions of nice pinned data from Hecke–Tate $L$-functions, from Rankin–Selberg integrals, and from twists of induced data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_isNicePinned_of_entire_pair.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.Converse.isNicePinned_of_entire_pair
    {ι : Type*} (D : LDatum ι) (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ)
    (hwf : D.WellFormed) (hconv : D.Converges) (hN : 0 < N)
    (hΛS : ∃ s : ℂ, D.abscissa < s.re ∧ ΛS s ≠ 0)
    (Λ₀ Λ₀d : ℂ → ℂ)
    (hΛ₀ : Differentiable ℂ Λ₀) (hbv : LDatum.BoundedOnStrips Λ₀)
    (hfe : ∀ s : ℂ, Λ₀ s = Λ₀d (2 * (D.center : ℂ) - s))
    (hmain : ∀ s : ℂ, D.abscissa < s.re → Λ₀ s = ΛS s * D.archFactor s * D.LFun s)
    (hmainDual : ∀ s : ℂ, D.abscissa < s.re →
      Λ₀d s = ε * (N : ℂ) ^ (s - (D.center : ℂ)) * ΛSd s * D.archFactorDual s * D.LFunDual s) :
    IsNicePinned D ΛS ΛSd ε N := by sorry
