-- Prove2me | Theorems.Thm_ModularCurve_periodMap_heckeTLin
-- name    : ModularCurve.periodMap_heckeTLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/00e2c8d1-db2b-5951-9cfd-16ea8da25df7
-- title:
--   Hecke equivariance of the period map in weight two
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell$ prime and $\ell \nmid N$ (so $N \neq 0$), and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Write $\mathrm{periodMap}\ N$ for the map sending a weight-two cusp form $g$ to the additive character of $\Gamma_0(N)$ obtained, by a choice, from some $F : \mathbb{H} \to \mathbb{C}$ with $F \circ \mathrm{ofComplex}$ having derivative $g(\tau)$ at each $\tau$, with $F \to 0$ along $\mathrm{Im} \to \infty$, with all coboundaries $z \mapsto F(\gamma z) - F(z)$, $\gamma \in \Gamma_0(N)$, constant, and with $F \circ \delta$ having a limit at $i\infty$ for every $\delta \in \mathrm{SL}_2(\mathbb{Z})$; the associated character is $\gamma \mapsto F(\gamma z) - F(z)$, viewed as an element of $\mathrm{Additive}\,\Gamma_0(N) \to_+ \mathbb{C}$ (the value is $0$ if no such $F$ exists). The assertion is that the period character of [`CuspForm.heckeTLin 2 hℓ hℓN f`](def/ModularForm_HeckeOperatorForms.html#L69), the cusp form whose underlying function is $\mathrm{heckeU}\ 2\ \ell\ f + f \mid[2] \mathrm{heckeDiagMatrix}\ \ell$, equals the image of the period character of $f$ under [`HeckeEis.heckeOperatorHom N ℓ ℂ`](def/Gamma0HeckeOperatorHom.html#L285): pull back along the homomorphism $\mathrm{heckeConj}\ N\ \ell$ from $(\mathrm{heckeUpperSL}\ \ell) \cap \Gamma_0(N)$ into $\Gamma_0(N)$ given by conjugation by $\mathrm{heckeConjMat}\ \ell$, then corestrict (transfer) back to $\Gamma_0(N)$ by summing over the coset space.
--
--   This is the Hecke equivariance half of the Eichler–Shimura construction in weight two: the analytic operator $T_\ell$ on $S_2(\Gamma_0(N))$ corresponds, under passage to periods, to the group-cohomological Hecke operator on $\mathrm{Hom}(\Gamma_0(N), \mathbb{C}) = H^1(\Gamma_0(N), \mathbb{C})$ built from conjugation and transfer. It is used in assembling the Hecke-equivariant map from cusp forms into $H^1$ and in the resulting faithful action of the Hecke algebra on parabolic cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_heckeTLin.lean

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.periodMap_heckeTLin {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) := by sorry
