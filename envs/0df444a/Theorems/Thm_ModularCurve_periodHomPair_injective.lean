-- Prove2me | Theorems.Thm_ModularCurve_periodHomPair_injective
-- name    : ModularCurve.periodHomPair_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/6debfdba-4f93-5933-aa91-9e1e8036d63c
-- title:
--   Injectivity of the Eichler–Shimura period pair map
-- statement:
--   Let $N$ be a natural number that is nonzero. The assertion is that the $\mathbb{C}$-linear map [`ModularCurve.periodHomPair N`](def/ModularCurve_PeriodHomPair.html#L135) from $\mathrm{CuspForm}(\Gamma_0(N),2) \times \mathrm{CuspForm}(\Gamma_0(N),2)$ to the additive homomorphisms $\mathrm{Additive}(\Gamma_0(N)) \to_{+} \mathbb{C}$ is injective, i.e. a pair of weight-two cusp forms on $\Gamma_0(N)$ mapping to the zero homomorphism is the zero pair. By definition, `periodHomPair N` is the zero map unless the predicate `ExistsPeriodMapLinear N` holds, that is, unless some $\mathbb{C}$-linear map $\mathrm{pml} \colon \mathrm{CuspForm}(\Gamma_0(N),2) \to (\mathrm{Additive}(\Gamma_0(N)) \to_{+} \mathbb{C})$ satisfies $\mathrm{pml}(f) = \mathrm{periodMap}\,N\,f$ for every $f$; in that case it is the coproduct of $(\mathrm{id} + \iota) \circ \mathrm{pml}$ and $(\mathrm{id} - \iota) \circ \mathrm{pml}$ for a chosen such $\mathrm{pml}$, where $\iota$ is the involution `charInvolution` sending $\psi$ to its precomposition with the additive form of the group endomorphism `jConjGamma0 N` of $\Gamma_0(N)$. Thus the pair $(f,g)$ is sent to $\gamma \mapsto (\mathrm{periodMap}\,N\,f)(\gamma) + (\mathrm{periodMap}\,N\,f)(\mathrm{jConj}\,\gamma) + (\mathrm{periodMap}\,N\,g)(\gamma) - (\mathrm{periodMap}\,N\,g)(\mathrm{jConj}\,\gamma)$, and the statement is that this vanishes identically only for $f = g = 0$. The proof cites the existence of an equivariant primitive with the required limit behaviour at the cusps, the identification of `periodMap` with the period homomorphism of such a primitive, and the validity of `ExistsPeriodMapLinear N`.
--
--   This is the injectivity half of the Eichler–Shimura isomorphism in weight two, in the form that the pair map $S_2(\Gamma_0(N))^{2} \to \mathrm{Hom}(\Gamma_0(N), \mathbb{C})$ built from the period homomorphism and its twist by the complex-conjugation involution has trivial kernel. It is used to compute the range of `periodHomPair` as the parabolic homomorphisms, to establish the Eichler–Shimura comparison itself, and in the vanishing criterion for Hecke words on cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodHomPair_injective.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.periodHomPair_injective (N : ℕ) [NeZero N] :
    Function.Injective (ModularCurve.periodHomPair N) := by sorry
