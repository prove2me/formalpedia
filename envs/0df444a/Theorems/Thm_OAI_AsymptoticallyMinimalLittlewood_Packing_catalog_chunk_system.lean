-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_catalog_chunk_system
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.catalog_chunk_system
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:29:53.115458+00:00
-- url     : https://prove2.me/theorems/d17d02db-09e6-40e9-b936-5f080a82adbe
-- title:
--   Chunk labelling of the catalog of signed interior sites modulo $q$
-- statement:
--   **Setting.** Let $r\ge1$ and $d:\{0,\dots,r-1\}\to\mathbb N$, with odd slot lengths $L_i=2d_i+1$, period length $P=\sum_{i<r}L_i$ and prefixes $\pi_i=\sum_{j<i}L_j$. Fix natural numbers $R$ (periods per chunk), $K$ (number of chunks) and $q\ge1$. The center of slot $i$ in period $p$ of chunk $k$ after a shift $s$ is $c(s,k,p,i)=kRP+pP+s+\pi_i+d_i+1$. For a sign $e\in\{+,-\}$ and $x\in\mathbb N$ let $\sigma_q(e,x)\in\mathbb Z/q\mathbb Z$ be the residue of $x$ if $e=+$ and of $-x$ if $e=-$.
--
--   - *Slot choices.* A slot choice $\omega$ assigns to every chunk $k\in\{0,\dots,K-1\}$ a shift and a sign, $\omega(k)=(s_k,e_k)\in\{0,\dots,P-1\}\times\{+,-\}$.
--   - *Hits.* A residue $u\in\mathbb Z/q\mathbb Z$ is hit by slot $i$ under $\omega$ if $u=\sigma_q\big(e_k,c(s_k,k,p,i)\big)$ for some chunk $k\in\{0,\dots,K-1\}$ and some period $p\in\{0,\dots,R-2\}$.
--   - *Catalog.* For $k\in\{0,\dots,K-1\}$ and $t\in\{0,\dots,(R-2)P-1\}$ let $x(k,t)=kRP+P+1+t$ be the interior sites of chunk $k$. The catalog is the set $\mathcal C=\{\sigma_q(e,x(k,t))\}\subseteq\mathbb Z/q\mathbb Z$ of all their signed residues, over all triples $(k,t,e)$.
--   - *Short residues.* For $B\in\mathbb N$ let $\mathcal S_B=\{c\bmod q:\ c\in\mathbb Z,\ |c|\le B\}$.
--
--   **Theorem.** Assume $K\ge1$ and $2KRP<q$, and fix a slot index $i_0$. Then there is a map $\chi:\mathbb Z/q\mathbb Z\to\{0,\dots,K-1\}$, assigning a chunk to every residue, such that
--
--   1. $\chi\big(\sigma_q(e,x(k,t))\big)=k$ for every catalog triple $(k,t,e)$;
--   2. for every slot $i$ and every $u\in\mathcal C$ there is a pair $\alpha_{i,u}\in\{0,\dots,P-1\}\times\{+,-\}$ such that, for every slot choice $\omega$, the residue $u$ is hit by slot $i$ under $\omega$ if and only if $\omega(\chi(u))=\alpha_{i,u}$;
--   3. for every chunk $k$, $\ |\{u\in\mathbb Z/q\mathbb Z:\ \chi(u)=k\}|\le q-|\mathcal C|+2(R-2)P$;
--   4. for all $u,v\in\mathcal C$ with $\chi(u)=\chi(v)$, at least one of $u+v$ and $u-v$ lies in $\mathcal S_{RP}$.
--
--   In particular, by item 2 the hit indicator of each catalog residue depends on a single coordinate of the slot choice:
--
--   $$
--   \mathbf 1\big[u\text{ is hit by slot } i\text{ under }\omega\big]=\mathbf 1\big[\omega(\chi(u))=\alpha_{i,u}\big]\qquad(u\in\mathcal C).
--   $$
--
--   These four properties are the combinatorial input for the variance estimate of random slot configurations: hit events of catalog residues are governed by single coordinates of $\omega$, each chunk class is small, and two catalog residues can share a coordinate only if they come from the same chunk, in which case their sum or difference is short.
--
--   **Formalization Note** Signs are Booleans and $\sigma_q$ is `signedSite`; the catalog is `catalogSet d R K q`, the image of `catalogValue` on `InteriorCatalog d R K = Fin K × Fin ((R-2) * P) × Bool`; slot choices are `SlotChoices d K`, hits are `slotHit`, and $\mathcal S_B$ is `shortResidues q B`. The hypothesis `[NeZero q]` encodes $q\ge1$, the subtraction in item 3 is natural-number subtraction (harmless since $|\mathcal C|\le q$), and $R-2$ is truncated subtraction. The slot $i_0$ only serves to guarantee $r\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean#L375-L432

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uJ
open scoped BigOperators
open Finset
variable {r : ℕ}

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.catalog_chunk_system (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i₀ : Fin r)
    (hK : 0<K) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    ∃ chunk : ZMod q → Fin K,
      (∀ c : InteriorCatalog d R K, chunk (catalogValue d R K q c)=c.1) ∧
      (∀ i t, t∈catalogSet d R K q →
        ∃ a : Fin (periodLength (oddLengths d)) × Bool,
          ∀ ω : SlotChoices d K, slotHit d R K q i ω t ↔ ω (chunk t)=a) ∧
      (∀ k, (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)).card≤
        q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) ∧
      (∀ t∈catalogSet d R K q, ∀ u∈catalogSet d R K q, chunk t=chunk u →
        t+u∈shortResidues q (R*periodLength (oddLengths d)) ∨
        t-u∈shortResidues q (R*periodLength (oddLengths d))) := by sorry
