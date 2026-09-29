-- Prove2me | Theorems.Thm_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen
-- name    : ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/2033c64c-1882-5dd9-b021-0d29b8c25478
-- title:
--   Mod p eigensystems occur, up to twist, in H¹
-- statement:
--   Let $p$ be a prime, let $N'\ge 1$ be an integer with $p\nmid N'$, let $S_0$ be a finite set of natural numbers with $p\in S_0$, and let $F$ be a field of characteristic $p$. Let $k$ be an integer with $k\ge 2$, let $\varphi\in F[[q]]$ and let $\lambda:\mathbb N\to F$. Assume $\varphi$ lies in [`ModPForms.modPMod N' k F`](def/CuspForm_ModPForms.html#L12), the $F$-span of those power series $\mathrm{mk}\,(n\mapsto (a_n\bmod p))$ arising from a modular form $f$ of weight $k$ on $\Gamma_0(N')$ whose $q$-expansion coefficients (at width $1$) are the integers $a_n$; and assume [`ModPForms.IsModPEigen N' S₀ k φ lam`](def/CuspForm_ModPForms.html#L24), that is, $\varphi\ne 0$ and for every prime $\ell$ with $\ell\nmid N'$ and $\ell\notin S_0$ the series with $n$-th coefficient $c_{n\ell}(\varphi)+[\ell\mid n]\,\ell^{\,k-1}c_{n/\ell}(\varphi)$ equals $\lambda(\ell)\varphi$. Then there exists $j\in\mathbb N$ such that the scaled system $\ell\mapsto \ell^{\,j}\lambda(\ell)$ (with $\ell$ the image of $\ell$ in $F$) is an eigensystem on the first cohomology of $\Gamma_0(N')$ acting on binary forms of degree $(k-2)_{\ge 0}$ over $F$, where the action is $P\mapsto P$ composed with the substitution $X_j\mapsto\sum_i g_{ij}X_i$ and the coefficient map at $\ell$ is substitution by $\mathrm{diag}(\ell,1)$. Explicitly, there is a nonzero class $x$ in the quotient of inhomogeneous $1$-cocycles by coboundaries for this representation such that for every prime $\ell$ with $\ell\nmid N'$, $\ell\notin S_0$ there is an $F$-linear endomorphism $T$ of that quotient which is induced by the cochain-level Hecke operator [`HeckeEis.coeffHeckeFun`](def/Gamma0CoeffCohomology.html#L129) at $\ell$ with coefficient part [`HeckeEis.binaryFormAlphaAdj F (k-2).toNat ℓ`](def/HeckeEis_BinaryFormRep.html#L82) (for each cocycle $z$ some cocycle $w$ equals that cochain and $T[z]=[w]$), and $T x = (\ell^{\,j}\lambda(\ell))\cdot x$.
--
--   This is the forms-to-cohomology direction of the Eichler–Shimura comparison, reduced modulo $p$ in the form used by Ash and Stevens: a mod $p$ eigensystem of weight $k$ on $\Gamma_0(N')$ is realised, after multiplication by a fixed power of $\ell$, on $H^1(\Gamma_0(N'),\mathrm{Sym}^{k-2})$ with coefficients in $F$. It feeds the step that replaces a mod $p$ eigenform of arbitrary weight by one of weight at most $4$, used in the passage from modularity to the Fermat equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen (p : ℕ) (hp : p.Prime)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀) (F : Type) [Field F] [CharP F p]
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries F) (lam : ℕ → F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) (heig : ModPForms.IsModPEigen N' S₀ k φ lam) :
    ∃ j : ℕ, HeckeEis.IsEigensystemH1 N'
      ((HeckeEis.binaryFormRepSL F (k - 2).toNat).comp (CongruenceSubgroup.Gamma0 N').subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F (k - 2).toNat ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ) := by sorry
