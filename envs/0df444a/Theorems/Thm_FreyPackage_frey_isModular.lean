-- Prove2me | Theorems.Thm_FreyPackage_frey_isModular
-- name    : FreyPackage.frey_isModular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1a989110-03d5-5923-bb48-be1c42b14f62
-- title:
--   Modularity of the Frey curve
-- statement:
--   The theorem takes a single input: a term $P$ of the project's structure [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17), i.e. nonzero integers $a,b,c$, a prime exponent $p\ge 5$, a solution $a^p+b^p=c^p$, the coprimality $\gcd(a,b)=1$, and the normalisations $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$. Its conclusion is `P.freyCurve.IsModular`, where `freyCurve` is the Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$, and where `IsModular` is the project's own predicate, unfolding as follows: there is a Weierstrass curve $W$ over $\mathbb{Z}$ which is an integral model of `P.freyCurve` in the sense that some variable change over $\mathbb{Q}$ carries `P.freyCurve` to the base change of $W$ to $\mathbb{Q}$, and there are a level $N>0$ and a cusp form $f$ of weight $2$ for $\Gamma_0(N)$ (Mathlib's `CuspForm`) satisfying the project's `IsNormalizedEigenform` — the $q$-expansion coefficients of $f$ at the cusp satisfy $a_1=1$, multiplicativity $a_{mn}=a_ma_n$ for coprime $m,n$, and the Hecke recursions $a_{\ell^{r+2}}=a_\ell a_{\ell^{r+1}}-\ell a_{\ell^{r}}$ for primes $\ell\nmid N$ and $a_{\ell^{r+2}}=a_\ell a_{\ell^{r+1}}$ for $\ell\mid N$ — such that for every prime $\ell$ with $\ell\nmid\Delta(W)$ and $\ell\nmid N$ one has $a_\ell(f)=\ell+1-\#(W\bmod \ell)(\mathbb{Z}/\ell)$, the point count being the cardinality of the Mathlib affine point type of the naive reduction of $W$ modulo $\ell$ (which includes the point at infinity). No minimality or conductor condition is imposed on $W$ or on $N$.
--
--   This is modularity of the Frey (Hellegouarch–Frey) curve attached to a putative Fermat solution, i.e. Wiles's modularity theorem for semistable elliptic curves over $\mathbb{Q}$ specialised to the Frey package. The formal conclusion is the project's coefficient-level notion of modularity — agreement of $\ell+1-\#W(\mathbb{F}_\ell)$ with the $\ell$-th $q$-coefficient of a normalised weight-$2$ eigenform on some $\Gamma_0(N)$ at primes of good reduction for the chosen integral model, with no claim that $N$ is the conductor and no $L$-function or modular parametrisation formulation. It is one of the four inputs to [`FreyPackage.no_frey_package`](thm.html#FreyPackage.no_frey_package), the statement that no Frey package exists, and is what makes level lowering applicable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_isModular.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem FreyPackage.frey_isModular (P : FreyPackage) : P.freyCurve.IsModular := by sorry
