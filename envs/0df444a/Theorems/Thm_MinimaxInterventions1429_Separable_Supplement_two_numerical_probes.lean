-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_two_numerical_probes
-- name    : MinimaxInterventions1429.Separable.Supplement.two_numerical_probes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:22:58.15312+00:00
-- url     : https://prove2.me/theorems/e2c5c648-abd8-404f-8e52-54580a74a93e
-- title:
--   Lemma A.1 — Two numerical probes
-- statement:
--   Let $L$ be cube-valued, $0<\lambda_0\le2$, $T_0=\lceil\log_2(2^{16}/\lambda_0)\rceil$, and $\eta_0=2^{-T_0}$. Coarse estimates satisfy $\|\widehat\omega-\omega(L)\|_\infty\le\eta_0$ and $\|M-(L-L_{g_01}\mathbf1)\|_\infty\le11\eta_0$. For distinct rows $g,r$ and distinct actions $h',h$, define the two clipped row differences $\widehat u,\widehat v$ and require $\widehat d=\widehat u-\widehat v\ge\lambda_0/16$. The literal probes are bounded separable queries, each with a unique exact minimizer supported on $\{h',h\}$ and with its $h$ coordinate in $[1/4,3/4]$. Their coordinates $x_0,x_1$ differ, and
--   $$\left(t_0+\widehat d/2-\frac{t_1-t_0}{x_1-x_0}x_0,\frac{t_1-t_0}{x_1-x_0}\right)=\bigl(L_{gh'}-L_{rh'},(L_{gh}-L_{gh'})-(L_{rh}-L_{rh'})\bigr).$$
--   This exact comparison refines the coarse two-anchor tree using two complete numerical responses.
--
--   Differences from the source:
--   - generalization: the estimates retained by the Appendix A coarse stage under its interaction promise → any estimates satisfying the stated eta_0 contrast and 11 eta_0 anchored coarse error bounds; reason: the numerical-probe argument uses only these bounds; the source coarse stage satisfies them
--   - encoding: two numerical probes → literal surcharges and total division with a nonzero-denominator conclusion; reason: weak bits remain available only in the coarse stage; complete exact mixtures determine the two signed differences
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma A.1, printed p.27 (PDF p.29)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Numerical
set_option autoImplicit false
universe u_two_numerical_probes

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem two_numerical_probes
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (L M w : Table m k) (hL : InCube L) (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 2)
    (root g r : Fin m) (h h' : Fin k) (hgr : g ≠ r) (hhh : h' ≠ h)
    (hw : entryNorm (w-contrasts L) ≤ eta (coarsePrecision lam))
    (hM : entryNorm (M-(fun s j => L s j-L root 0)) ≤ 11*eta (coarsePrecision lam))
    (hsep : lam/16 ≤ probeSeparation w g r h h') :
    (twoProbes M w g r h h').usesAtMost 2 ∧
    (twoProbes M w g r h h').queriesSatisfy Allowed ∧
    (∀ t ∈ ({probeT0 M g r h', probeT1 M w g r h h'} : Set ℝ),
      ∃ p : Mixture k, Optimal (L+numericalProbe w g r h h' t) 0 p ∧
        (∀ q, Optimal (L+numericalProbe w g r h h' t) 0 q → q=p) ∧
        (∀ j, j ≠ h' → j ≠ h → p.val j=0) ∧ 1/4 ≤ p.val h ∧ p.val h ≤ 3/4) ∧
    (∀ (p₀ p₁ : Mixture k),
      Optimal (L+numericalProbe w g r h h' (probeT0 M g r h')) 0 p₀ →
      Optimal (L+numericalProbe w g r h h' (probeT1 M w g r h h')) 0 p₁ →
      p₁.val h ≠ p₀.val h ∧
      decodeProbes M w g r h h' (p₀.val h) (p₁.val h) =
        (L g h'-L r h', (L g h-L g h')-(L r h-L r h'))) := by sorry

end MinimaxInterventions1429.Separable.Supplement
