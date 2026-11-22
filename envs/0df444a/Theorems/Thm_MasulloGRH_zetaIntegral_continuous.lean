-- Prove2me | Theorems.Thm_MasulloGRH_zetaIntegral_continuous
-- name    : MasulloGRH.zetaIntegral_continuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:30.638794+00:00
-- url     : https://prove2.me/theorems/d220199f-fda2-4844-815e-d96a7db8a06b
-- title:
--   Lemma 3.2.2.3 — for $\sigma(c)>1$ the global zeta integral $f\mapsto Z(f,c)$ is a continuous linear functional on $\mathcal S(\mathbb A_F)$
-- statement:
--   **The global zeta integrals are tempered distributions** (Lemma 3.2.2.3 of the source).
--
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring, $\mathrm{GL}_1(\mathbb A_F)$ the idele group with the idelic norm $|\cdot|_F$ and the Tamagawa measure $\mu$, and $\mathcal S(\mathbb A_F)$ the Schwartz–Bruhat space with its locally convex inductive limit topology. Let $c$ be a quasi-character of the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$, i.e. a continuous homomorphism $\mathrm{GL}_1(\mathbb A_F)\to\mathbb C^\times$ trivial on $F^\times$, with abscissa $\sigma(c)=\sigma$, i.e. $|c(g)|=|g|_F^{\sigma}$ for all ideles $g$.
--
--   If $\sigma>1$, then the linear functional
--   $$\mathcal S(\mathbb A_F)\to\mathbb C,\qquad f\mapsto Z(f,c)=\int_{\mathrm{GL}_1(\mathbb A_F)}f(g)\,c(g)\,d\mu(g)$$
--   is continuous.
--
--   So $Z(\cdot,c)$ is a tempered distribution on $\mathbb A_F$ for every quasi-character $c$ of $C_F$ with $\sigma(c)>1$ (the set $\Omega(C_F)_{>1}$ of the source). In the source this is the first step towards regarding $c\mapsto Z(\cdot,c)$ as a meromorphic family of distributions (Weil's eigendistributions, §3.4); its proof is the model for the $S$-local Lemma 3.3.1.3.
--
--   **Formalization Note.** The abscissa is given as a real number $\sigma$ with $|c|=|\cdot|_F^\sigma$ (it exists and is unique for every quasi-character of $C_F$). Continuity is for the platform topology of `AdelicSchwartz F`; the measure is the platform Tamagawa measure `tamagawaIdele F`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 125, Lemma 3.2.2.3 (proof pp. 125–126)

import Mathlib
import Definitions.Def_MasulloGRH_ZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem zetaIntegral_continuous
    (F : Type*) [Field F] [NumberField F] (c : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c)
    (σ : ℝ) (hσ : ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ) (h1 : 1 < σ) :
    Continuous (fun f : AdelicSchwartz F => zetaIntegral f c) := by sorry

end MasulloGRH
