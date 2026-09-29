-- Prove2me | Theorems.Thm_Garrido_hasInvariantExtensionProperty_of_isAmenable
-- name    : Garrido.hasInvariantExtensionProperty_of_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:35:00.186047+00:00
-- url     : https://prove2.me/theorems/0bf3524a-e23e-4619-abfd-96d6f28107e5
-- title:
--   Theorem 2.6 — the Invariant Extension Theorem
-- statement:
--   If $G$ is amenable then $G$ has the invariant extension property: for every
--   $G$-set $X$, every $G$-invariant family $R$ of subsets of $X$, every $G$-invariant $\mu$ on
--   $R$, and every finitely additive $\nu$ on all of $\mathcal{P}(X)$ extending $\mu$, there is a
--   finitely additive **$G$-invariant** $\bar\mu$ on $\mathcal{P}(X)$ that still extends $\mu$.
--
--   The unrestricted extension $\nu$ appears as a hypothesis rather than being constructed. This
--   follows the source, which *recalls* Carathéodory's extension theorem for finitely additive
--   measures on a Boolean algebra ("If $\mathcal{R}$ is a subring of the boolean algebra $\mathcal{A}$ and $\mu$ is a
--   measure on $\mathcal{R}$, then $\mu$ can be extended to a measure $\bar\mu$ on
--   $\mathcal{A}$") and then supplies
--   only the invariance. The theorem's content is therefore that amenability upgrades an arbitrary
--   extension to an invariant one.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorem 2.6 (Invariant Extension Theorem). The source recalls Carathéodory's extension theorem for finitely additive measures on a Boolean algebra rather than proving it; accordingly the unrestricted extension is a hypothesis of the formalised statement; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem hasInvariantExtensionProperty_of_isAmenable {G : Type*} [Group G]
    (hG : IsAmenable G) :
    HasInvariantExtensionProperty G := by
  sorry

end Garrido
