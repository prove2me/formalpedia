-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_transport_original_ray_compensatedPhysicalProbe_low_loss
-- name    : OAI.SevenEighths.ProbePhysical.transport_original_ray_compensatedPhysicalProbe_low_loss
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T04:04:36.936531+00:00
-- url     : https://prove2.me/theorems/b6e06cf1-45a5-4a95-9e01-2ae5670a6140
-- title:
--   Low-side bound $Z^{x/2+(y-x)/12+\mathrm{loss}}$ for the compensated physical probe with free exponents
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$ and all objects are those of OpenAI's family-003 development of the quasi-Riemann hypothesis for Hecke characters of $\mathbb Q(\zeta_3)$.
--
--   **Exponents.** Let $E,x,y$ be real numbers with
--   $$
--   0\le E\le\tfrac15,\qquad x+y=1-E,\qquad x<y,\qquad E<2x-y .
--   $$
--
--   **Data.** Let $S$ be a finite set of ideals of $\mathcal O$ satisfying the source exclusions, all of whose members are maximal. Let $\ell_1,\dots,\ell_K\ge0$ be pairwise distinct with $\sum_i\ell_i\le E$, let $R$ be any set of ideals, and let $0<a\le b$. Let $W_1,\dots,W_K:\mathbb R\to\mathbb C$ be supported in $[a,b]$ with $\lvert W_i\rvert\le B$. Let $W_0,W_1^\ast:\mathbb R\to\mathbb C$ be smooth, supported in $[a_0,b_0]$ and $[a_1,b_1]$ with $a_0,a_1>0$ and $a_1<b_1$, and bounded by $B_0,B_1\ge0$.
--
--   **The probe.** For $Z>0$ let $T_i(Z)$ be the set of prime ideals $P\in R$, $P\notin S$, with $\lfloor aZ^{\ell_i}\rfloor<N(P)\le\lfloor bZ^{\ell_i}\rfloor$, and let $J_\eta(Z)$ be the compensated physical probe of a Hecke character $\eta$: the sum, over tuples $(p_1,\dots,p_K)$ of primary generators of primes $P_i\in T_i(Z)$, of
--   $$
--   \prod_{i=1}^K W_i\!\Big(\frac{N(p_i)}{Z^{\ell_i}}\Big)\cdot \mathrm{comp}_\eta\big(p_1,\dots,p_K;\,Z^{x},Z^{y},Z\big),
--   $$
--   where $\mathrm{comp}_\eta$ is the compensated tuple term built from $W_0,W_1^\ast$ and the calibration data attached to $S$, with row scale $X=Z^x$ and column scale $Y=Z^y$.
--
--   **Statement.** For every $\mathrm{loss}>0$ and every Hecke character $\eta$ there is $C>0$ such that for all sufficiently large $Z$,
--   $$
--   \lvert J_\eta(Z)\rvert\le C\,Z^{\,x/2+(y-x)/12+\mathrm{loss}} .
--   $$
--
--   This is the low-side bound for the unnormalized probe with the total slot width and the two geometric exponents left as parameters. OpenAI's original statement is the case of its fixed exponents; LW56e2's transport carries that argument over to all $(E,x,y)$ satisfying the four displayed constraints.
--
--   **Formalization Note** $J_\eta(Z)$ is `compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1 (fun i => canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i => Z^(ell i)) (Z^x) (Z^y) Z`. Distinctness of the $\ell_i$ is `Function.Injective ell`. The constant $C$ may depend on all the data, on $\eta$ and on the loss.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalLow/LowWindowBound.lean, theorem OAI.SevenEighths.ProbePhysical.transport_original_ray_compensatedPhysicalProbe_low_loss (L18-L34): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalLow/LowWindowBound.lean#L18-L34

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
set_option autoImplicit false
open scoped Classical ContDiff SchwartzMap
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => OAI.ActualEisensteinCubic.O
local notation "Id" => Ideal O
noncomputable section

theorem OAI.SevenEighths.ProbePhysical.transport_original_ray_compensatedPhysicalProbe_low_loss
    (totalWidth x y : ℝ) (hE0 : 0≤totalWidth) (hE1 : totalWidth≤1/5)
    (hsumXY : x+y=1-totalWidth) (hxy : x<y) (hgrow : totalWidth<2*x-y)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤totalWidth) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^x) (Z^y) Z‖≤C*Z^((x/2+(y-x)/12)+loss) := by sorry
